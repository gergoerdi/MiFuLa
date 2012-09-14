{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.TC where

import Mifula.Fresh
import Mifula.Syntax
import Mifula.Unify.UVar
import Mifula.Unify (UnificationError)
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Monoid
import Prelude hiding (foldr)
import Data.Foldable (foldMap, foldr)

newtype TC a = TC{ unTC :: SupplyId a }
             deriving (Functor, Applicative, Monad)

lookupPolyVar :: Var Scoped -> TC (Maybe Typing)
lookupPolyVar = undefined

lookupCon :: Con Scoped -> TC (Tagged Ty Typed)
lookupCon = undefined

newtype MonoEnv = MonoEnv{ monoVarMap :: Map (Var Scoped) (Tagged Ty Typed) }
                deriving Monoid

instance SubstUVars MonoEnv (Tv Typed) where
    θ ▷ m = MonoEnv . fmap (θ ▷) . monoVarMap $ m

instance HasUVars MonoEnv (Tv Typed) where
    uvars = foldMap uvars . monoVarMap

monoVar :: Var Scoped -> Tagged Ty Typed -> Typing
monoVar x τ = τ :@ m
  where
    m = MonoEnv $ Map.singleton x τ

monoVars :: MonoEnv -> Set (Var Scoped)
monoVars = Map.keysSet . monoVarMap

removeMonoVars :: Set (Var Scoped) -> MonoEnv -> MonoEnv
removeMonoVars xs = MonoEnv . (foldr Map.delete `flip` xs) . monoVarMap

lookupMonoVar :: Var Scoped -> MonoEnv -> Maybe (Tagged Ty Typed)
lookupMonoVar x = Map.lookup x . monoVarMap

instance MonadFresh (Tv Typed) TC where
    fresh = TvFresh <$> TC fresh

data Typing = Tagged Ty Typed :@ MonoEnv

instance SubstUVars Typing (Tv Typed) where
    θ ▷ (τ :@ m) = (θ ▷ τ) :@ (θ ▷ m)

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m
