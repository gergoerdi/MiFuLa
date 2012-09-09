{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
module Mifula.Unify.UEq where

import Mifula.Unify.UVar
import Mifula.Syntax

data UEq a = a :~: a
           deriving (Show, Functor)

instance SubstUVars a ξ => SubstUVars (UEq a) ξ where
    θ ▷ (x :~: y) = (θ ▷ x) :~: (θ ▷ y)

sym :: UEq a -> UEq a
sym (x :~: y) = (y :~: x)

data Unification ξ a = Congruent
                     | Substitute ξ a
                     | Recurse [UEq a]
                     | Incongruent
                     | Flip
                     deriving Show

class (SubstUVars a ξ) => Unify a ξ | a -> ξ where
    unify1 :: UEq a -> Unification ξ a

instance Unify (Kind In) Kv where
    unify1 eq = case eq of
        KVar α    :~:  κ           -> Substitute α κ
        _         :~:  KVar α      -> Flip
        KStar     :~:  KStar       -> Congruent
        KArr κ μ  :~:  KArr κ' μ'  -> Recurse [κ :~: κ', μ :~: μ']
        _                          -> Incongruent

instance Unify (Tagged Ty Typed) (Tv Typed) where
    unify1 eq = case eq of
        T _ (TyVar α)    :~: tτ                              -> Substitute α tτ
        _                :~: T _ (TyVar α)                   -> Flip
        T _ (TyCon con)  :~: T _ (TyCon con') | con == con'  -> Congruent
        T _ TyFun        :~: T _ TyFun                       -> Congruent
        T _ (TyApp t u)  :~: T _ (TyApp t' u')               -> Recurse [t :~: t', u :~: u']
        _                                                    -> Incongruent
