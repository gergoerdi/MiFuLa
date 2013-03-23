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
import Control.Arrow ((&&&))
import Data.Monoid
import Control.Monad.Trans.Either
import Control.Monad.Trans (lift)
import Control.Monad (forM, liftM)

data UnificationError ξ a = ErrIncongruent (UEq a)
                          | ErrOccurs ξ a
                          deriving Show

unifyEqs :: forall m a ξ. (UTerm ξ ~ a, Unify m a ξ, HasUVars a ξ)
         => Bool -> [UEq a] -> m (Either (UEq a, UnificationError ξ a) (Subst ξ))
unifyEqs allowFlip = runEitherT . go . map dup
  where
    dup :: forall a. a -> (a, a)
    dup = id &&& id

    go :: [(UEq a, UEq a)] -> EitherT (UEq a, UnificationError ξ a) m (Subst ξ)
    go [] = return mempty
    go ((src, eq):eqs) = lift (unify1 eq) >>= \res -> case res of
        Congruent -> go eqs
        Substitute x t -> case contract x t mempty of
            Nothing -> throw $ ErrOccurs x t
            Just θ -> do
                eqs' <- forM eqs $ \(src, eq) -> do
                    eq' <- lift $ θ ▷ eq
                    return (src, eq')
                liftM (θ <>) $ go eqs'
        Recurse eqs' ->
            go $ map (src,) eqs' ++ eqs
        Incongruent ->
            throw $ ErrIncongruent eq
        Flip | allowFlip -> go $ (src, sym eq):eqs
             | otherwise -> throw $ ErrIncongruent eq -- Maybe we can do better...
      where
        throw err = left (src, err)
