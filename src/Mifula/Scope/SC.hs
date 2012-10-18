{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Mifula.Scope.SC
       ( SC, runSC
       , freshBinding
       , refVar, refCon, refTyCon
       , refVarB, refConB, refTyConB
       , refTv
       , freshVar, defVar, defPVar
       , listenVars, withVars, listenPVars
       , withBoundTyVars, withTyVars
       , atPosition
       ) where

import Mifula.Syntax
import Mifula.Prims
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
                | SEUnresolvedTyVar (Tv Parsed)
                | SEPatternConflict (Var Parsed)
                deriving Show

data R = R{ rVars :: Map (VarB Parsed) (VarB Scoped)
          , rTyVars :: Maybe (Map (Tv Parsed) (Tv Scoped))
          , rCons :: Map (ConB Parsed) (ConB Scoped)
          , rTyCons :: Map (TyConB Parsed) (TyConB Scoped)
          , rPos :: SourcePos
          }

instance Default R where
    def = R{ rVars = mempty
           , rTyVars = Nothing
           , rCons = mempty
           , rTyCons = mempty
           , rPos = noPos
           }

data W = W{ wRefs :: Set (VarB Scoped)
          , wPVars :: Set (VarB Scoped)
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

withId :: Binding ns Parsed -> Id -> Binding ns Scoped
(BindName s) `withId` x = BindId s x

unId :: Binding ns Scoped -> Binding ns Parsed
unId (BindId s _) = BindName s

runSC :: [TyDef Parsed] -> SC a -> Either [(SourcePos, ScopeError)] a
runSC tydefs sc = case runSupplyId $ evalRWST (unSC sc') def def of
    (x, w) -> case wErrors w of
        [] -> Right x
        errs -> Left errs
  where
    tycons :: Set (TyConB Parsed)
    tycons = Set.fromList $ map tcName tydefs
    tcName (TDAlias name _ _) = name
    tcName (TDData name _ _) = name

    cons :: Set (ConB Parsed)
    cons = Set.fromList $ concatMap conName tydefs
    conName (TDAlias _ _ _) = []
    conName (TDData _ _ cons) = map ((\(ConDef con _) -> con) . unTag) cons

    sc' = do
        tycons' <- genIds tycons
        cons' <- genIds cons
        SC . local (\r -> r{ rCons = cons', rTyCons = tycons' }) . unSC $ sc

    genIds :: Set (Binding ns Parsed) -> SC (Map (Binding ns Parsed) (Binding ns Scoped))
    genIds refs = fmap Map.fromAscList $ forM (Set.toAscList refs) $ \bind -> do
        x <- fresh
        return (bind, bind `withId` x)

listenVars :: Set (VarB Scoped) -> SC a -> SC (a, Set (VarB Scoped))
listenVars newVars = listenRefs (`Set.member` newVars) . withVars newVars

withVars :: Set (VarB Scoped) -> SC a -> SC a
withVars newVars = SC . local addVars . unSC
  where
    addVars :: R -> R
    addVars r@R{ rVars } = r{ rVars = newVarMap `Map.union` rVars }

    newVarMap :: Map (VarB Parsed) (VarB Scoped)
    newVarMap = Map.fromList . map (unId &&& id) $ Set.toList newVars

withBoundTyVars :: Set (Tv Scoped) -> SC a -> SC a
withBoundTyVars newTvs = SC . local addTyVars . unSC
  where
    addTyVars :: R -> R
    addTyVars r@R{ rTyVars } = r{ rTyVars = rTyVars' }
      where
        rTyVars' = Just $ newMap `Map.union` (mempty `fromMaybe` rTyVars)

    newMap :: Map (Tv Parsed) (Tv Scoped)
    newMap = Map.fromList . map ((TvNamed . unId . unT) &&& id) $ Set.toList newTvs

    unT (TvNamed name) = name

withTyVars :: SC a -> SC a
withTyVars = SC . localS clearTyVars . unSC
  where
    localS f m = do
        s <- get
        put $ f s
        y <- m
        put s
        return y

    clearTyVars :: S -> S
    clearTyVars s = s{ sTyVars = mempty }

listenRefs :: (Binding NSVar Scoped -> Bool) -> SC a -> SC (a, Set (Binding NSVar Scoped))
listenRefs isLocal sc = do
    (x, w) <- SC . censor noRefs . listen . unSC $ sc
    let vars = wRefs w
        (varsHere, varsThere) = Set.partition isLocal vars
    SC . tell $ mempty{ wRefs = varsThere }
    return (x, varsHere)
  where
    noRefs :: W -> W
    noRefs w = w{ wRefs = mempty }

listenPVars :: SC a -> SC (a, Set (Binding NSVar Scoped))
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
tellVar ref = case ref of
    BindingRef x -> SC . tell $ mempty{ wRefs = Set.singleton x }
    PrimRef _ -> return ()

tellPVar :: VarB Scoped -> SC ()
tellPVar x = SC . tell $ mempty{ wPVars = Set.singleton x }

refAssert sel err x@(BindingRef name) = do
    mbind <- SC . asks $ Map.lookup name . sel
    case mbind of
        Nothing -> do
            case resolvePrim name of
                Nothing -> do
                    scopeError $ err x
                    return $ error "unresolved"
                Just ref -> return ref
        Just bind -> return $ BindingRef bind

refPredefined sel x = do
    mbind <- SC . asks $ Map.lookup x . sel
    case mbind of
        Nothing -> internalError $ unwords ["Pre-defined reference not found:", show x]
        Just bind -> return bind

refVarB :: VarB Parsed -> SC (VarB Scoped)
refVarB = refPredefined rVars

refVar :: Var Parsed -> SC (Var Scoped)
refVar x@(BindingRef name) = do
    ref <- refAssert rVars SEUnresolvedVar x
    tellVar ref
    return ref

refCon :: Con Parsed -> SC (Con Scoped)
refCon = refAssert rCons SEUnresolvedCon

internalError :: String -> SC a
internalError s = error $ unwords ["Internal error:", s]

refConB :: ConB Parsed -> SC (ConB Scoped)
refConB = refPredefined rCons

refTyCon :: TyCon Parsed -> SC (TyCon Scoped)
refTyCon = refAssert rTyCons SEUnresolvedTyCon

refTyConB :: TyConB Parsed -> SC (TyConB Scoped)
refTyConB = refPredefined rTyCons

refTv :: Tv Parsed -> SC (Tv Scoped)
refTv tv@(TvNamed ref) = do
    mtyvars <- SC . asks $ rTyVars
    case mtyvars of
        Just tyvars -> case Map.lookup tv tyvars of
            Nothing -> do
                scopeError $ SEUnresolvedTyVar tv
                return $ error "unresolved"
            Just tv' -> return tv'
        Nothing -> do
            mtv <- SC . gets $ Map.lookup tv . sTyVars
            case mtv of
                Nothing -> do
                    id <- freshBinding ref
                    let tv' = TvNamed id
                    SC . modify $ addTv tv'
                    return tv'
                Just tv' -> do
                    return tv'
  where
    addTv :: Tv Scoped -> S -> S
    addTv tv' s@S{ sTyVars } = s{ sTyVars = Map.insert tv tv' sTyVars }

freshBinding :: Binding ns Parsed -> SC (Binding ns Scoped)
freshBinding ref = do
    x <- fresh
    return $ ref `withId` x

freshVar :: VarB Parsed -> SC (VarB Scoped)
freshVar = freshBinding

defVar :: VarB Parsed -> SC (VarB Scoped)
defVar x = SC $ asks $ force . Map.lookup x . rVars
  where
    force = fromMaybe (error "Internal error: unresolved def")

defPVar :: VarB Parsed -> SC (VarB Scoped)
defPVar var = do
    ref <- freshVar var
    tellPVar ref
    return ref
