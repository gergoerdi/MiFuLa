{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
module Mifula.Unify.UEq where

import Mifula.Unify.UVar
import Mifula.Syntax
import Control.Monad (liftM2)

data UEq a = a :~: a
           deriving (Show, Functor)

instance SubstUVars m a ξ => SubstUVars m (UEq a) ξ where
    θ ▷ (x :~: y) = liftM2 (:~:) (θ ▷ x) (θ ▷ y)

sym :: UEq a -> UEq a
sym (x :~: y) = (y :~: x)

data Unification ξ a = Congruent
                     | Substitute ξ a
                     | Recurse [UEq a]
                     | Incongruent
                     | Flip
                     deriving Show

class (SubstUVars m a ξ) => Unify m a ξ | a -> ξ where
    unify1 :: UEq a -> m (Unification ξ a)

instance (Monad m) => Unify m (Kind In) Kv where
    unify1 eq = return $ case eq of
        KVar α    :~:  κ           -> Substitute α κ
        _         :~:  KVar α      -> Flip
        KStar     :~:  KStar       -> Congruent
        KArr κ μ  :~:  KArr κ' μ'  -> Recurse [κ :~: κ', μ :~: μ']
        _                          -> Incongruent

instance (Monad m) => Unify m (Tagged Ty Typed) (Tv Typed) where
    unify1 eq = return $ case eq of
        T _ (TyVar α)    :~: tτ                              -> Substitute α tτ
        _                :~: T _ (TyVar α)                   -> Flip
        T _ (TyCon con)  :~: T _ (TyCon con') | con == con'  -> Congruent
        T _ TyFun        :~: T _ TyFun                       -> Congruent
        T _ (TyApp t u)  :~: T _ (TyApp t' u')               -> Recurse [t :~: t', u :~: u']
        _                                                    -> Incongruent
