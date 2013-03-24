{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.MonoEnv
       ( Typing(..), MonoEnv
       , prettyTyping
       , monoVar, monoVars
       , overloadedTy
       , removeMonoVars, lookupMonoVar
       ) where

import Mifula.Syntax
import Mifula.Unify.UVar
import Mifula.Typing.Constraint
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode ((⊆))
import Data.Monoid
import Prelude hiding (foldr, mapM)
import Data.Foldable (foldMap, foldr)
import Data.Traversable (mapM)
import Control.Monad (forM, liftM, liftM2, unless)
import Control.Applicative ((<$>))

import Mifula.Syntax.Pretty ()
import Mifula.Syntax.Readable
import Text.PrettyPrint.Leijen hiding ((<$>), (<>))

infix 1 :@
data Typing = Tagged Ty Typed :@ MonoEnv
            deriving Show

prettyTyping :: Typing -> Readable Doc
prettyTyping (τ :@ m) = do
    ctxt <- prettyMonoConstraints m
    vars <- prettyMonoVars m
    τ' <- readableTyT τ
    return $ maybe id prependCtxt ctxt $ maybe id prependVars vars $ pretty τ'
  where
    prependCtxt ctxt d = ctxt <+> text "⇒" <+> d
    prependVars vars d = vars <+> text "⊢" <+> d

instance (MonadConstraint m) => SubstUVars m Typing (Tv Typed) where
    θ ▷ (τ :@ m) = liftM2 (:@) (θ ▷ τ) (θ ▷ m)

instance HasUVars Typing (Tv Typed) where
    uvars (τ :@ m) = uvars τ <> uvars m

-- TODO: the keys in the map should be `Id`s, not `Var`s (since they
-- should never be `PrimRef`s).
-- However, this would cause problems with trying to print a
-- `MonoEnv`, since we need string names there.
data MonoEnv = MonoEnv{ monoVarMap :: Map (VarB (Kinded Out)) (Tagged Ty Typed)
                      , monoConstraints :: Constraints Out
                      }
             deriving (Show)

instance Monoid MonoEnv where
    mempty = MonoEnv mempty mempty
    (MonoEnv vars cs) `mappend` (MonoEnv vars' cs') = MonoEnv (vars <> vars') (cs <> cs')

prettyMonoVars :: MonoEnv -> Readable (Maybe Doc)
prettyMonoVars m
  | Set.null (monoVars m) = return Nothing
  | otherwise = do
      vars <- forM (Map.toList . monoVarMap $ m) $ \(var, τ) -> do
          τ' <- readableTyT τ
          return (var, τ')
      return . Just $ enclose . map (uncurry prettyMono) $ vars
  where
    enclose = encloseSep lbrace rbrace comma
    prettyMono var τ = pretty var <+> text "∷" <+> pretty τ

prettyMonoConstraints :: MonoEnv -> Readable (Maybe Doc)
prettyMonoConstraints m = prettyConstraints (monoConstraints m)

instance (MonadConstraint m) => SubstUVars m MonoEnv (Tv Typed) where
    θ ▷ m = liftM2 MonoEnv (mapM (θ ▷) $ monoVarMap m) (θ ▷ monoConstraints m)

instance HasUVars MonoEnv (Tv Typed) where
    uvars = foldMap uvars . monoVarMap

monoVar :: VarB (Kinded Out) -> Tagged Ty Typed -> Typing
monoVar x τ = τ :@ m
  where
    m = MonoEnv (Map.singleton x τ) mempty

overloadedTy :: [Constraint Out] -> Tagged Ty Typed -> Typing
overloadedTy ctxt τ = τ :@ m
  where
    m = MonoEnv mempty $ Constraints ctxt

monoVars :: MonoEnv -> Set (VarB (Kinded Out))
monoVars = Map.keysSet . monoVarMap

removeMonoVars :: (MonadConstraint m) => Set (VarB (Kinded Out)) -> MonoEnv -> m MonoEnv
removeMonoVars xs (MonoEnv vars cs) = do
    let vars' = foldr Map.delete vars xs
    unless (uvars cs ⊆ foldMap uvars vars') $
      -- TODO: proper error reporting
      error "Amigbuous constraint"
    return $ MonoEnv vars' cs

lookupMonoVar :: VarB (Kinded Out) -> MonoEnv -> Maybe (Tagged Ty Typed)
lookupMonoVar x = Map.lookup x . monoVarMap
