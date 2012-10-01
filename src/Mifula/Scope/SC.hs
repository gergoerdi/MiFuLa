{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Mifula.Scope.SC
       ( SC, runSC
       , freshRef
       , refVar, refCon, refTyCon, refTv
       , freshVar, defVar, defPVar
       , listenVars, withVars, listenPVars, withTyVars
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
import Control.Arrow ((&&&))
import Data.Default

data ScopeError = SEUnresolvedCon (Con Parsed)
                | SEUnresolvedTyCon (TyCon Parsed)
                | SEUnresolvedVar (Var Parsed)
                | SEPatternConflict (Var Parsed)
                deriving Show

data R = R{ rVars :: Map (Var Parsed) (Var Scoped)
          , rCons :: Map (Con Parsed) (Con Scoped)
          , rTyCons :: Map (TyCon Parsed) (TyCon Scoped)
          , rPos :: SourcePos
          }

instance Default R where
    def = R{ rVars = mempty
           , rCons = mempty
           , rTyCons = mempty
           , rPos = noPos
           }

data W = W{ wRefs :: Set (Var Scoped)
          , wPVars :: Set (Var Scoped)
          , wErrors :: [(SourcePos, ScopeError)]
          }

instance Monoid W where
    mempty = W mempty mempty mempty
    (W refs defs errors) `mappend` (W refs' defs' errors') = W (refs <> refs') (defs <> defs') (errors <> errors')

data S = S{ sTyVars :: Map (Tv Parsed) (Tv Scoped) }

instance Default S where
    def = S{ sTyVars = mempty }

newtype SC a = SC{ unSC :: RWST R W S SupplyId a }
             deriving (Functor, Applicative, Monad)

instance MonadFresh Id SC where
    fresh = SC . lift $ fresh

withId :: Ref Parsed -> Id -> Ref Scoped
(NameRef s) `withId` x = IdRef s x

unId :: Ref Scoped -> Ref Parsed
unId = NameRef . refName

runSC :: [TyDef Parsed] -> SC a -> Either [(SourcePos, ScopeError)] a
runSC tydefs sc = case runSupplyId $ evalRWST (unSC sc') def def of
    (x, w) -> case wErrors w of
        [] -> Right x
        errs -> Left errs
  where
    tycons :: Set (TyCon Parsed)
    tycons = Set.fromList $ map tcName tydefs
    tcName (TDAlias name _ _) = name
    tcName (TDData name _ _) = name

    cons :: Set (Con Parsed)
    cons = Set.fromList $ concatMap conName tydefs
    conName (TDAlias _ _ _) = []
    conName (TDData _ _ cons) = map ((\(ConDef con _) -> con) . unTag) cons

    sc' = do
        tycons' <- genIds tycons
        cons' <- genIds cons
        SC . local (\r -> r{ rCons = cons', rTyCons = tycons' }) . unSC $ sc

    genIds refs = fmap Map.fromAscList $ forM (Set.toAscList refs) $ \ref -> do
        x <- fresh
        return (ref, ref `withId` x)

listenVars :: Set (Var Scoped) -> SC a -> SC (a, Set (Var Scoped))
listenVars newVars = listenRefs (`Set.member` newVars) . withVars newVars

withVars :: Set (Var Scoped) -> SC a -> SC a
withVars newVars = SC . local addVars . unSC
  where
    addVars :: R -> R
    addVars r@R{ rVars } = r{ rVars = newVarMap `Map.union` rVars }

    newVarMap :: Map (Var Parsed) (Var Scoped)
    newVarMap = Map.fromList . map (unId &&& id) $ Set.toList newVars

withTyVars :: Set (Tv Scoped) -> SC a -> SC a
withTyVars newTvs = SC . localS addTyVars . unSC
  where
    localS f m = do
        s <- get
        put $ f s
        y <- m
        put s
        return y

    addTyVars :: S -> S
    addTyVars s@S{ sTyVars } = s{ sTyVars = newMap `Map.union` sTyVars }

    newMap :: Map (Tv Parsed) (Tv Scoped)
    newMap = Map.fromList . map ((TvNamed . unId . unT) &&& id) $ Set.toList newTvs

    unT (TvNamed name) = name

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

refAssert sel err x = do
    mref <- SC $ asks $ Map.lookup x . sel
    case mref of
        Nothing -> do
            scopeError $ err x -- TODO
            return $ error "unresolved"
        Just ref -> do
            return ref

refVar :: Var Parsed -> SC (Var Scoped)
refVar x = do
    ref <- refAssert rVars SEUnresolvedVar x
    tellVar ref
    return ref

refCon :: Con Parsed -> SC (Con Scoped)
refCon = refAssert rCons SEUnresolvedCon

refTyCon :: TyCon Parsed -> SC (TyCon Scoped)
refTyCon = refAssert rTyCons SEUnresolvedTyCon

refTv :: Tv Parsed -> SC (Tv Scoped)
refTv tv@(TvNamed ref) = do
    mtv <- SC . gets $ Map.lookup tv . sTyVars
    case mtv of
        Nothing -> do
            id <- freshRef ref
            let tv' = TvNamed id
            SC . modify $ addTv tv'
            return tv'
        Just tv' -> do
            return tv'
  where
    addTv :: Tv Scoped -> S -> S
    addTv tv' s@S{ sTyVars } = s{ sTyVars = Map.insert tv tv' sTyVars }

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
