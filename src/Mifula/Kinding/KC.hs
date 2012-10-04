{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
module Mifula.Kinding.KC where

import Mifula.Syntax
import Mifula.Unify
import Mifula.Unify.UVar
import Mifula.Unify.UEq

import Control.Applicative
import Control.Monad.RWS
import Mifula.Fresh
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Default
import Data.Monoid

data R = R{ rTyCons :: Map (TyCon Scoped) (Kind In)
          , rTyVars :: Map (Tv Scoped) (Kind In)
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

-- TODO: error handling
newtype KC a = KC{ unKC :: RWST R [UEq (Kind In)] () SupplyId a }
             deriving (Functor, Applicative, Monad)

instance MonadFresh Kv KC where
    fresh = KC . lift $ fresh

runKC :: KC a -> a
runKC kc = runSupplyId $ fmap fst $ evalRWST (unKC kc) def ()

withTyCons :: Map (TyCon Scoped) (Kind In) -> KC a -> KC a
withTyCons tyCons = KC . local addTyCons . unKC
  where
    addTyCons :: R -> R
    addTyCons r@R{ rTyCons } = r{ rTyCons = tyCons <> rTyCons }

withTyVars :: Map (Tv Scoped) (Kind In) -> KC a -> KC a
withTyVars tyVars = KC . local addTyVars . unKC
  where
    addTyVars :: R -> R
    addTyVars r@R{ rTyVars } = r{ rTyVars = tyVars <> rTyVars }

lookupTyVar :: Tv Scoped -> KC (Kind In)
lookupTyVar α = do
    mκ <- KC . asks $ Map.lookup α . rTyVars
    maybe fail return mκ
  where
    fail = internalError $ unwords ["type variable not found:", show α]

lookupTyCon :: TyCon Scoped -> KC (Kind In)
lookupTyCon α = do
    mκ <- KC . asks $ Map.lookup α . rTyCons
    maybe fail return mκ
  where
    fail = internalError $ unwords ["type constructor not found:", show α]

assert :: UEq (Kind In) -> KC ()
assert = KC . tell . (:[])

-- TODO: copypasta from TC
internalError :: String -> KC a
internalError s = error $ unwords ["Internal error:", s]

unified :: KC a -> KC (a, Subst Kv)
unified m = do
    (x, eqs) <- KC . censor (const mempty) . listen . unKC $ m
    -- case unifyEqs True eqs of
    --     Left (eq, err) -> do
    --         error (show err) -- TODO
    --     Right θ -> return (x, θ)
    return (x, mempty)
