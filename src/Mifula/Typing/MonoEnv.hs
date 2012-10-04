{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.MonoEnv
       ( Typing(..), MonoEnv
       , prettyTyping, prettyMonoEnv
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
import Control.Monad (forM)
import Control.Applicative ((<$>))

import Mifula.Syntax.Pretty ()
import Mifula.Syntax.Readable
import Text.PrettyPrint.Leijen hiding ((<$>), (<>))

data Typing = Tagged Ty Typed :@ MonoEnv
            deriving Show

prettyTyping :: Typing -> Readable Doc
prettyTyping (τ :@ m)
  | Set.null (monoVars m) = pretty <$> readableTyT τ
  | otherwise = do
      τ' <- readableTyT τ
      env <- prettyMonoEnv m
      return $ env <+> text "⊢" <+> pretty τ'

instance SubstUVars Typing (Tv Typed) where
    θ ▷ (τ :@ m) = (θ ▷ τ) :@ (θ ▷ m)

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m

newtype MonoEnv = MonoEnv{ monoVarMap :: Map (Var (Kinded Out)) (Tagged Ty Typed) }
                deriving (Monoid, Show)

prettyMonoEnv :: MonoEnv -> Readable Doc
prettyMonoEnv m = do
    vars <- forM (Map.toList . monoVarMap $ m) $ \(var, τ) -> do
        τ' <- readableTyT τ
        return (var, τ')
    return $ enclose . map (uncurry prettyMono) $ vars
  where
    enclose = encloseSep lbrace rbrace comma
    prettyMono var τ = pretty var <+> text "∷" <+> pretty τ

instance SubstUVars MonoEnv (Tv Typed) where
    θ ▷ m = MonoEnv . fmap (θ ▷) . monoVarMap $ m

instance HasUVars MonoEnv (Tv Typed) where
    uvars = foldMap uvars . monoVarMap

monoVar :: Var (Kinded Out) -> Tagged Ty Typed -> Typing
monoVar x τ = τ :@ m
  where
    m = MonoEnv $ Map.singleton x τ

monoVars :: MonoEnv -> Set (Var (Kinded Out))
monoVars = Map.keysSet . monoVarMap

removeMonoVars :: Set (Var (Kinded Out)) -> MonoEnv -> MonoEnv
removeMonoVars xs = MonoEnv . (foldr Map.delete `flip` xs) . monoVarMap

lookupMonoVar :: Var (Kinded Out) -> MonoEnv -> Maybe (Tagged Ty Typed)
lookupMonoVar x = Map.lookup x . monoVarMap
