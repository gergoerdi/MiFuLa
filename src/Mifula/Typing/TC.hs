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

newtype PolyEnv = PolyEnv{ unPolyEnv :: Map (Var Scoped) Typing }
                deriving (Show, Monoid)

instance SubstUVars PolyEnv (Tv Typed) where
    θ ▷ env = PolyEnv . fmap (θ ▷) . unPolyEnv $ env

polyVar :: Var Scoped -> Typing -> PolyEnv
polyVar x tyg = PolyEnv $ Map.singleton x tyg

polyVars :: PolyEnv -> Set (Var Scoped)
polyVars = Map.keysSet . unPolyEnv

generalize :: Set (Var Scoped) -> PolyEnv -> PolyEnv
generalize vars = PolyEnv . fmap restrict . unPolyEnv
  where
    restrict :: Typing -> Typing
    restrict (τ :@ m) = τ :@ removeMonoVars vars m

data R = R{ rCons :: Map (Con Scoped) (Tagged Ty Typed)
          , rPolyEnv :: PolyEnv
          }
       deriving Show

newtype TC a = TC{ unTC :: ReaderT R SupplyId a }
             deriving (Functor, Applicative, Monad)

runTC :: Map (Con Scoped) (Tagged Ty Typed)
      -> PolyEnv
      -> TC a -> a -- TODO: errors
runTC cons polyEnv tc = runSupplyId $ runReaderT (unTC tc) r
  where
    r = R{ rCons = cons
         , rPolyEnv = polyEnv
         }

internalError :: String -> TC a
internalError s = error $ unwords ["Internal error:", s]

-- noteError :: UnificationError (Tv Typed) (Tagged Ty Typed) -> TC ()
-- noteError = undefined

lookupPolyVar :: Var Scoped -> TC (Maybe Typing)
lookupPolyVar var = TC . asks $ Map.lookup var . unPolyEnv . rPolyEnv

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

