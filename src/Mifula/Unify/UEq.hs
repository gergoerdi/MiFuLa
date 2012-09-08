{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
module Mifula.Unify.UEq where

import Mifula.Unify.UVar
import Mifula.Syntax

data UEq a = a :~: a
           deriving (Show, Functor)

data Unification ξ a = Congruent
                     | Substitute ξ a
                     | Recurse [UEq a]
                     | Incongruent
                     | Flip

class (SubstUVars a ξ) => Unify a ξ | a -> ξ where
    unify :: UEq a -> Unification ξ a

instance Unify (Kind In) Kv where
    unify eq = case eq of
        KVar α    :~:  κ           -> Substitute α κ
        _         :~:  KVar α      -> Flip
        KStar     :~:  KStar       -> Congruent
        KArr κ μ  :~:  KArr κ' μ'  -> Recurse [κ :~: κ', μ :~: μ']
        _                          -> Incongruent

instance Unify (Tagged Ty Typed) (Tv Typed) where
    unify eq = case eq of
        T _ (TyVar α)    :~: tτ                              -> Substitute α tτ
        _                :~: T _ (TyVar α)                   -> Flip
        T _ (TyCon con)  :~: T _ (TyCon con') | con == con'  -> Congruent
        T _ TyFun        :~: T _ TyFun                       -> Congruent
        T _ (TyApp t u)  :~: T _ (TyApp t' u')               -> Recurse [t :~: t', u :~: u']
        _                                                    -> Incongruent
