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

import Control.Monad.Reader

data Typing = Tagged Ty Typed :@ MonoEnv
            deriving Show

instance SubstUVars Typing (Tv Typed) where
    θ ▷ (τ :@ m) = (θ ▷ τ) :@ (θ ▷ m)

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m

-- Since we are past scope checking here, every variable has an Id
-- key, so we might as well use an IntMap if it turns out to be more
-- performant.

data R = R{ rCons :: Map (Con Scoped) (Tagged Ty Typed)
          , rPolyVars :: Map (Var Scoped) Typing
          }
       deriving Show

newtype TC a = TC{ unTC :: ReaderT R SupplyId a }
             deriving (Functor, Applicative, Monad)

runTC :: Map (Con Scoped) (Tagged Ty Typed)
      -> Map (Var Scoped) Typing
      -> TC a -> a -- TODO: errors
runTC cons polyVars tc = runSupplyId $ runReaderT (unTC tc) r
  where
    r = R{ rCons = cons
         , rPolyVars = polyVars
         }

internalError :: String -> TC a
internalError s = error $ unwords ["Internal error:", s]

-- noteError :: UnificationError (Tv Typed) (Tagged Ty Typed) -> TC ()
-- noteError = undefined

lookupPolyVar :: Var Scoped -> TC (Maybe Typing)
lookupPolyVar var = TC . asks $ Map.lookup var . rPolyVars

lookupCon :: Con Scoped -> TC (Tagged Ty Typed)
lookupCon con =
    (TC . asks $ Map.lookup con . rCons) >>=
    maybe (internalError $ unwords ["constructor not found:", show con]) return

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

instance MonadFresh (Tv Typed) TC where
    fresh = TvFresh <$> (TC . lift $ fresh)

