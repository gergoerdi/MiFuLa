{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeFamilies #-}
module Mifula.Unify.UVar
       ( Subst
       , UVar(..), HasUVars(..), SubstUVars(..)
       , occurs
       , contract, resolve
       ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class Ord ξ => UVar a ξ | a -> ξ where
    injectVar :: ξ -> a
    isVar :: a -> ξ -> Bool

newtype Subst ξ a = Subst{ uvMap :: Map ξ a }

class UVar a ξ => HasUVars a ξ | a -> ξ where
    uvars :: a -> Set ξ

class HasUVars a ξ => SubstUVars a ξ | a -> ξ where
    (▷) :: Subst ξ a -> a -> a

occurs :: (HasUVars a ξ) => ξ -> a -> Bool
occurs x ty = x `Set.member` uvars ty

-- | Contract the varible α with the term t, i.e. add a substitution t/α
contract :: (HasUVars a ξ) => ξ -> a -> Subst ξ a -> Maybe (Subst ξ a)
contract α t θ | t `isVar` α = Just θ
               | occurs α t = Nothing
               | otherwise = Just θ'
  where
    θ' = Subst $ Map.insert α t $ uvMap θ

-- | Resolve the variable α into a term
resolve :: (SubstUVars a ξ) => ξ -> Subst ξ a -> a
resolve α θ = case Map.lookup α (uvMap θ) of
    Nothing -> injectVar α
    Just t -> θ ▷ t
