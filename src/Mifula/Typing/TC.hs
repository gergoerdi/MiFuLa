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
import Data.Foldable (foldMap)

newtype TC a = TC{ unTC :: SupplyId a }
             deriving (Functor, Applicative, Monad)

newtype MonoEnv = MonoEnv{ monoVarMap :: Map (Var Scoped) (Tagged Ty Typed) }
                deriving Monoid

instance SubstUVars MonoEnv (Tv Typed) where
    θ ▷ m = MonoEnv . fmap (θ ▷) . monoVarMap $ m

instance HasUVars MonoEnv (Tv Typed) where
    uvars = foldMap uvars . monoVarMap

monoVar :: Var Scoped -> Tagged Ty Typed -> Typing
monoVar = undefined

monoVars :: MonoEnv -> Set (Var Scoped)
monoVars = undefined

removeMonoVars :: Set (Var Scoped) -> MonoEnv -> MonoEnv
removeMonoVars = undefined

lookupMonoVar :: Var Scoped -> MonoEnv -> Maybe (Tagged Ty Typed)
lookupMonoVar = undefined

instance MonadFresh (Tv Typed) TC where
    fresh = TvFresh <$> TC fresh

data Typing = Tagged Ty Typed :@ MonoEnv

instance SubstUVars Typing (Tv Typed) where
    θ ▷ (τ :@ m) = undefined

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m

lookupPolyVar :: Var Scoped -> TC (Maybe Typing)
lookupPolyVar = undefined

lookupCon :: Con Scoped -> TC (Tagged Ty Typed)
lookupCon = undefined
