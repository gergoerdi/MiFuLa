{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.PolyEnv
       ( PolyEnv
       , polyVar, polyVars
       , polyMonos, lookupPolyVar
       , generalize
       ) where

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

newtype PolyEnv = PolyEnv{ unPolyEnv :: Map (Var Kinded) Typing }
                deriving (Show, Monoid)

instance SubstUVars PolyEnv (Tv Typed) where
    θ ▷ env = PolyEnv . fmap (θ ▷) . unPolyEnv $ env

instance Pretty PolyEnv where
    pretty = vcat . map (uncurry var) . Map.toList . unPolyEnv
      where
        var x tyg = pretty x <+> text "∷" <+> pretty tyg

polyVar :: Var Kinded -> Typing -> PolyEnv
polyVar x tyg = PolyEnv $ Map.singleton x tyg

polyVars :: PolyEnv -> Set (Var Kinded)
polyVars = Map.keysSet . unPolyEnv

polyMonos :: PolyEnv -> [MonoEnv]
polyMonos = map (\(τ :@ m) -> m) . Map.elems . unPolyEnv

lookupPolyVar :: Var Kinded -> PolyEnv -> Maybe Typing
lookupPolyVar var = Map.lookup var . unPolyEnv

generalize :: Set (Var Kinded) -> PolyEnv -> PolyEnv
generalize vars = PolyEnv . fmap restrict . unPolyEnv
  where
    restrict :: Typing -> Typing
    restrict (τ :@ m) = τ :@ removeMonoVars vars m
