{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Mifula.Typing.Subst (Subst, addSubst, substTv) where

import Mifula.Syntax

import Control.Monad.Writer
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Default

class HasTypeVars a where
    tvs :: a -> Set Tv

occurs :: (HasTypeVars a) => Tv -> a -> Bool
occurs x ty = x `Set.member` tvs ty

class HasTypeVars a => SubstTypeVars a where
    (▷) :: Subst -> a -> a

instance HasTypeVars (Ty π) where
    tvs = execWriter . go
      where
        collect = tell . Set.singleton

        go τ = case τ of
            TyVar α -> collect α
            TyApp t u -> go (unTag t) >> go (unTag u)
            _ -> return ()

instance HasTypeVars (Tagged Ty π) where
    tvs = tvs . unTag

instance SubstTypeVars (Tagged Ty Typed) where
    θ ▷ tτ = case unTag tτ of
        TyCon con -> tτ
        TyVar α -> substTv α θ
        TyApp tt tu -> T (tag tτ) $ TyApp (θ ▷ tt) (θ ▷ tu)
        TyFun -> tτ

newtype Subst = Subst{ tvMap :: Map Tv (Tagged Ty Typed) }

addSubst :: Tv -> Tagged Ty Typed -> Subst -> Maybe Subst
addSubst α tτ θ = case unTag tτ of
    TyVar β | β == α -> Just θ
    τ | occurs α τ -> Nothing
      | otherwise -> Just θ'
  where
    θ' = Subst $ Map.insert α tτ $ tvMap θ

substTv :: Tv -> Subst -> Tagged Ty Typed
substTv α θ = case Map.lookup α (tvMap θ) of
    Nothing -> T def $ TyVar α
    Just tτ -> θ ▷ tτ
