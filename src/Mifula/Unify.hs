{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Unify where

import Mifula.Unify.UVar
import Mifula.Unify.UEq
import Control.Arrow ((&&&), second)
import Data.Monoid

data UnificationError ξ a = ErrIncongruent (UEq a)
                          | ErrOccurs ξ a
                          deriving Show

unifyEqs :: forall a ξ. (UTerm ξ ~ a, Unify a ξ, HasUVars a ξ)
         => Bool -> [UEq a] -> Either (UEq a, UnificationError ξ a) (Subst ξ)
unifyEqs allowFlip = go . map (id &&& id)
  where
    go :: [(UEq a, UEq a)] -> Either (UEq a, UnificationError ξ a) (Subst ξ)
    go [] = return mempty
    go ((src, eq):eqs) = case unify1 eq of
        Congruent -> go eqs
        Substitute x t -> case contract x t mempty of
            Nothing -> throw $ ErrOccurs x t
            Just θ -> fmap (θ <>) $ go $ map (second (θ ▷)) eqs
        Recurse eqs' ->
            go $ map (src,) eqs' ++ eqs
        Incongruent ->
            throw $ ErrIncongruent eq
        Flip | allowFlip -> go $ (src, sym eq):eqs
             | otherwise -> throw $ ErrIncongruent eq -- Maybe we can do better...
      where
        throw err = Left (src, err)
