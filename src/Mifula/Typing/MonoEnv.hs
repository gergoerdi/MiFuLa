{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.MonoEnv
       ( Typing(..), MonoEnv
       , monoVar, monoVars
       , removeMonoVars, lookupMonoVar
       ) where

import Mifula.Syntax
import Mifula.Unify.UVar
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Prelude hiding (foldr)
import Data.Foldable (foldMap, foldr)

import Mifula.Syntax.Pretty ()
import Text.PrettyPrint.Leijen hiding ((<$>), (<>))

data Typing = Tagged Ty Typed :@ MonoEnv
            deriving Show

instance Pretty Typing where
    pretty (τ :@ m) = if Set.null (monoVars m) then pretty τ
                      else pretty m <+> text "⊢" <+> pretty τ

instance SubstUVars Typing (Tv Typed) where
    θ ▷ (τ :@ m) = (θ ▷ τ) :@ (θ ▷ m)

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m

newtype MonoEnv = MonoEnv{ monoVarMap :: Map (Var Scoped) (Tagged Ty Typed) }
                deriving (Monoid, Show)

instance Pretty MonoEnv where
    pretty = enclose . map (uncurry prettyMono) . Map.toList . monoVarMap
      where
        enclose = encloseSep lbrace rbrace comma
        prettyMono var τ = pretty var <+> text "∷" <+> pretty τ

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
