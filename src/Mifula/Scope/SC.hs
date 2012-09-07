{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Mifula.Scope.SC
       ( SC, runSC
       , refVar, refCon, freshVar, defVar, defPVar
       , listenVars, withVars, listenPVars
       , atPosition
       ) where

import Mifula.Syntax
import Mifula.Fresh

import Control.Error
import Control.Monad.RWS
import Control.Applicative
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream
import Control.Arrow (first, second, (&&&))
import Data.Default

data ScopeError = SEUnresolvedCon (Con Parsed)
                | SEUnresolvedVar (Var Parsed)
                | SEPatternConflict (Var Parsed)
                deriving Show

data R = R{ rVars :: Map (Var Parsed) (Var Scoped)
          , rCons :: Map (Con Parsed) (Con Scoped)
          , rPos :: SourcePos
          }

data W = W{ wRefs :: Set (Var Scoped)
          , wPVars :: Set (Var Scoped)
          , wErrors :: [(SourcePos, ScopeError)]
          }

instance Monoid W where
    mempty = W mempty mempty mempty
    (W refs defs errors) `mappend` (W refs' defs' errors') = W (refs <> refs') (defs <> defs') (errors <> errors')

newtype SC a = SC{ unSC :: RWS R W (Stream Id) a }
             deriving (Functor, Applicative, Monad)

instance MonadFresh Id SC where
    fresh = SC $ do
        Cons x xs <- get
        put xs
        return x

withId :: Ref Parsed -> Id -> Ref Scoped
(NameRef s) `withId` x = IdRef s x

unId :: Ref Scoped -> Ref Parsed
unId = NameRef . refName

runSC :: Set (Con Parsed) -> SC a -> Either [(SourcePos, ScopeError)] a
runSC cons sc = case evalRWS (unSC sc') r₀ s₀ of
    (x, w) -> case wErrors w of
        [] -> Right x
        errs -> Left errs
  where
    r₀ = R{ rVars = mempty
          , rCons = mempty
          , rPos = noPos
          }

    sc' = do
        cons' <- fmap Map.fromAscList $ forM (Set.toAscList cons) $ \con -> do
            x <- fresh
            return $ (con, con `withId` x)
        SC . local (\r -> r{ rCons = cons' }) . unSC $ sc

    s₀ = Stream.iterate succ (toEnum 0)

listenVars :: Set (Var Scoped) -> SC a -> SC (a, Set (Var Scoped))
listenVars newVars = listenRefs (`Set.member` newVars) . withVars newVars

withVars :: Set (Var Scoped) -> SC a -> SC a
withVars newVars = SC . local addVars . unSC
  where
    addVars :: R -> R
    addVars r@R{ rVars } = r{ rVars = newVarMap `Map.union` rVars }

    newVarMap :: Map (Var Parsed) (Var Scoped)
    newVarMap = Map.fromList . map (unId &&& id) $ Set.toList newVars

listenRefs :: (Var Scoped -> Bool) -> SC a -> SC (a, Set (Var Scoped))
listenRefs isLocal sc = do
    (x, w) <- SC . censor noRefs . listen . unSC $ sc
    let vars = wRefs w
        (varsHere, varsThere) = Set.partition isLocal vars
    SC . tell $ mempty{ wRefs = varsThere }
    return (x, varsHere)
  where
    noRefs :: W -> W
    noRefs w = w{ wRefs = mempty }

listenPVars :: SC a -> SC (a, Set (Var Scoped))
listenPVars sc = do
    (x, w) <- SC . censor noPVars . listen . unSC $ sc
    return (x, wPVars w)
  where
    noPVars :: W -> W
    noPVars w = w{ wPVars = mempty }

atPosition :: SourcePos -> SC a -> SC a
atPosition pos = SC . local setPos . unSC
  where
    setPos r = r{ rPos = pos }

scopeError :: ScopeError -> SC ()
scopeError err = do
    pos <- SC . asks $ rPos
    SC . tell $ mempty{ wErrors = [(pos, err)]} -- TODO: error locations

tellVar :: Var Scoped -> SC ()
tellVar x = SC . tell $ mempty{ wRefs = Set.singleton x }

tellPVar :: Var Scoped -> SC ()
tellPVar x = SC . tell $ mempty{ wPVars = Set.singleton x }

refVar :: Var Parsed -> SC (Var Scoped)
refVar x = do
    mref <- SC $ asks $ Map.lookup x . rVars
    case mref of
        Nothing -> do
            scopeError $ SEUnresolvedVar x -- TODO
            return $ error "unresolved"
        Just ref -> do
            tellVar ref
            return ref

refCon :: Con Parsed -> SC (Var Scoped)
refCon con = do
    mref <- SC $ asks $ Map.lookup con . rCons
    case mref of
        Nothing -> do
            scopeError $ SEUnresolvedCon con
            return $ error "unresolved"
        Just ref -> do
            return ref

freshRef :: Ref Parsed -> SC (Ref Scoped)
freshRef ref = do
    x <- fresh
    return $ ref `withId` x

freshVar :: Var Parsed -> SC (Var Scoped)
freshVar = freshRef

defVar :: Var Parsed -> SC (Var Scoped)
defVar x = SC $ asks $ force . Map.lookup x . rVars
  where
    force = fromMaybe (error "Internal error: unresolved def")

defPVar :: Var Parsed -> SC (Var Scoped)
defPVar var = do
    ref <- freshVar var
    tellPVar ref
    return ref
