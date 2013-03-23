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
import Mifula.Syntax.Readable
import Mifula.Unify.UVar
import Mifula.Typing.MonoEnv
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Monoid
import Prelude hiding (mapM)
import Data.Traversable (mapM)
import Control.Monad (liftM)

import Mifula.Syntax.Pretty ()
import Text.PrettyPrint.Leijen hiding ((<$>))

-- Since we are past scope checking here, every variable has an Id
-- key, so we might as well use an IntMap if it turns out to be more
-- performant.

newtype PolyEnv = PolyEnv{ unPolyEnv :: Map (VarB (Kinded Out)) Typing }
                deriving (Show, Monoid)

instance (Monad m) => SubstUVars m PolyEnv (Tv Typed) where
    θ ▷ env = liftM PolyEnv . mapM (θ ▷) . unPolyEnv $ env

instance Pretty PolyEnv where
    pretty = vcat . map (uncurry var) . Map.toList . unPolyEnv
      where
        var x tyg = pretty x <+> text "∷" <+> runReadable (prettyTyping tyg)

polyVar :: VarB (Kinded Out) -> Typing -> PolyEnv
polyVar x tyg = PolyEnv $ Map.singleton x tyg

polyVars :: PolyEnv -> Set (VarB (Kinded Out))
polyVars = Map.keysSet . unPolyEnv

polyMonos :: PolyEnv -> [MonoEnv]
polyMonos = map (\(τ :@ m) -> m) . Map.elems . unPolyEnv

lookupPolyVar :: VarB (Kinded Out) -> PolyEnv -> Maybe Typing
lookupPolyVar var = Map.lookup var . unPolyEnv

generalize :: Set (VarB (Kinded Out)) -> PolyEnv -> PolyEnv
generalize vars = PolyEnv . fmap restrict . unPolyEnv
  where
    restrict :: Typing -> Typing
    restrict (τ :@ m) = τ :@ removeMonoVars vars m
