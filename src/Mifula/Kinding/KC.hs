{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
module Mifula.Kinding.KC where

import Mifula.Syntax
import Mifula.Prims
import Mifula.Unify
import Mifula.Unify.UVar
import Mifula.Unify.UEq

import Control.Applicative
import Control.Monad.RWS
import Control.Monad.Trans.Either
import Mifula.Fresh
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Default
import Data.Monoid

data R = R{ rTyCons :: Map Id (Kind In)
          , rTyVars :: Map Id (Kind In)
          }

instance Default R where
    def = R{ rTyCons = mempty
           , rTyVars = mempty
           }

data W = W{ wEqs :: [UEq (Kind In)]
          }

instance Monoid W where
    mempty = W{ wEqs = mempty }
    (W eqs) `mappend` (W eqs') = W (eqs <> eqs')

newtype KC a = KC{ unKC :: RWST R [UEq (Kind In)] () (EitherT (UnificationError Kv (Kind In)) SupplyId) a }
             deriving (Functor, Applicative, Monad)

instance MonadFresh Kv KC where
    fresh = KC . lift . lift $ fresh

runKC :: KC a -> Either (UnificationError Kv (Kind In)) a
runKC kc = runSupplyId $ runEitherT $ fmap fst $ evalRWST (unKC kc) def ()

withTyCons :: Map Id (Kind In) -> KC a -> KC a
withTyCons tyCons = KC . local addTyCons . unKC
  where
    addTyCons :: R -> R
    addTyCons r@R{ rTyCons } = r{ rTyCons = tyCons <> rTyCons }

withTyVars :: Map Id (Kind In) -> KC a -> KC a
withTyVars tyVars = KC . local addTyVars . unKC
  where
    addTyVars :: R -> R
    addTyVars r@R{ rTyVars } = r{ rTyVars = tyVars <> rTyVars }

lookupTyVar :: Tv Scoped -> KC (Kind In)
lookupTyVar α@(TvNamed (IdRef _ x))  = do
    mκ <- KC . asks $ Map.lookup x . rTyVars
    maybe fail return mκ
  where
    fail = internalError $ unwords ["type variable not found:", show α]

demoteKind :: Kind Out -> Kind In
demoteKind κ = case κ of
    KStar -> KStar
    κ₁ `KArr` κ₂ -> demoteKind κ₁ `KArr` demoteKind κ₂

lookupTyCon :: TyCon Scoped -> KC (Kind In)
lookupTyCon (PrimRef _ p) = return . demoteKind $ primTyConKind p
lookupTyCon c@(IdRef _ x) = do
    mκ <- KC . asks $ Map.lookup x . rTyCons
    maybe fail return mκ
  where
    fail = internalError $ unwords ["type constructor not found:", show c]

assert :: UEq (Kind In) -> KC ()
assert = KC . tell . (:[])

-- TODO: copypasta from TC
internalError :: String -> KC a
internalError s = error $ unwords ["Internal error:", s]

unified :: KC a -> KC (a, Subst Kv)
unified m = do
    (x, eqs) <- KC . censor (const mempty) . listen . unKC $ m
    case unifyEqs True eqs of
        Left (eq, err) -> KC . lift . left $ err
        Right θ -> return (x, θ)
