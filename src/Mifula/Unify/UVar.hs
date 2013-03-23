{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
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
import Data.Monoid
import Prelude hiding (mapM)
import Data.Traversable (mapM)

class Ord ξ => UVar ξ where
    type UTerm ξ
    isVar :: UTerm ξ -> ξ -> Bool

newtype Subst ξ = Subst{ uvMap :: Map ξ (UTerm ξ) }
                  deriving Monoid
deriving instance (Show ξ, Show (UTerm ξ)) => Show (Subst ξ)

class UVar ξ => HasUVars a ξ where
    uvars :: a -> Set ξ

class (UVar ξ, Monad m) => SubstUVars m a ξ where
    (▷) :: Subst ξ -> a -> m a

instance SubstUVars m a ξ => SubstUVars m [a] ξ where
    θ ▷ xs = mapM (θ ▷) xs

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
resolve :: (SubstUVars m (UTerm ξ) ξ) => ξ -> Subst ξ -> m (Maybe (UTerm ξ))
resolve α θ = mapM (θ ▷) $ Map.lookup α (uvMap θ)
