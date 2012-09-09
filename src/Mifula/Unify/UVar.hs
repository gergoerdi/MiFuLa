{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
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

class Ord ξ => UVar ξ where
    type UTerm ξ
    isVar :: UTerm ξ -> ξ -> Bool

newtype Subst ξ = Subst{ uvMap :: Map ξ (UTerm ξ) }

class UVar ξ => HasUVars a ξ | a -> ξ where
    uvars :: a -> Set ξ

class UVar ξ => SubstUVars a ξ | a -> ξ where
    (▷) :: Subst ξ -> a -> a

instance SubstUVars a ξ => SubstUVars [a] ξ where
    θ ▷ xs = map (θ ▷) xs

occurs :: (HasUVars a ξ) => ξ -> a -> Bool
occurs x ty = x `Set.member` uvars ty

-- | Contract the varible α with the term t, i.e. add a substitution t/α
contract :: (UVar ξ, HasUVars (UTerm ξ) ξ)
         => ξ -> UTerm ξ -> Subst ξ -> Maybe (Subst ξ)
contract α t θ | t `isVar` α = Just θ
               | occurs α t = Nothing
               | otherwise = Just θ'
  where
    θ' = Subst $ Map.insert α t $ uvMap θ

-- | Resolve the variable α into a term
resolve :: (SubstUVars (UTerm ξ) ξ) => ξ -> Subst ξ -> Maybe (UTerm ξ)
resolve α θ = fmap (θ ▷) $ Map.lookup α (uvMap θ)
