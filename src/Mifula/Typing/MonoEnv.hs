{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.MonoEnv where

import Mifula.Syntax
import Mifula.Unify.UVar
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Monoid
import Prelude hiding (foldr)
import Data.Foldable (foldMap, foldr)

data Typing = Tagged Ty Typed :@ MonoEnv
            deriving Show

instance SubstUVars Typing (Tv Typed) where
    θ ▷ (τ :@ m) = (θ ▷ τ) :@ (θ ▷ m)

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m

newtype MonoEnv = MonoEnv{ monoVarMap :: Map (Var Scoped) (Tagged Ty Typed) }
                deriving (Monoid, Show)

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
