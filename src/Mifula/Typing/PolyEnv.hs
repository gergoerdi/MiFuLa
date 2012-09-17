{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.PolyEnv where

import Mifula.Syntax
import Mifula.Unify.UVar
import Mifula.Typing.MonoEnv
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Monoid

import Mifula.Syntax.Pretty ()
import Text.PrettyPrint.Leijen hiding ((<$>))

-- Since we are past scope checking here, every variable has an Id
-- key, so we might as well use an IntMap if it turns out to be more
-- performant.

newtype PolyEnv = PolyEnv{ unPolyEnv :: Map (Var Scoped) Typing }
                deriving (Show, Monoid)

instance SubstUVars PolyEnv (Tv Typed) where
    θ ▷ env = PolyEnv . fmap (θ ▷) . unPolyEnv $ env

instance Pretty PolyEnv where
    pretty = vcat . map (uncurry var) . Map.toList . unPolyEnv
      where
        var x (τ :@ m) = pretty x <+> text "::" <+> pretty τ

polyVar :: Var Scoped -> Typing -> PolyEnv
polyVar x tyg = PolyEnv $ Map.singleton x tyg

polyVars :: PolyEnv -> Set (Var Scoped)
polyVars = Map.keysSet . unPolyEnv

polyMonos :: PolyEnv -> [MonoEnv]
polyMonos = map (\(τ :@ m) -> m) . Map.elems . unPolyEnv

generalize :: Set (Var Scoped) -> PolyEnv -> PolyEnv
generalize vars = PolyEnv . fmap restrict . unPolyEnv
  where
    restrict :: Typing -> Typing
    restrict (τ :@ m) = τ :@ removeMonoVars vars m
