{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Mifula.Syntax
       ( Pass(..), AST(..), Tagged(..)
       , Id, Ref(..), Var, Con, TyCon
       , Ty(..), Tv(..)
       , Kv, InOut(..), Kind(..)
       , Expr(..), Pat(..)
       , Match(..), Def(..), Defs(..)
       , defName
       , SourcePos, noPos
       ) where

import Data.Default
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)
import Mifula.Unify.UVar

import Control.Monad.Writer hiding ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

data Pass = Parsed
          | Scoped
          | Kinded
          | Typed

class AST (a :: Pass -> *) where
    type Tag a (π :: Pass)
    type Tag a Parsed = TagParsed a
    type Tag a Scoped = TagScoped a
    type Tag a Kinded = TagKinded a
    type Tag a Typed = TagTyped a

    type TagParsed a
    type TagParsed a = SourcePos

    type TagScoped a
    type TagScoped a = Tag a Parsed

    type TagKinded a
    type TagKinded a = Tag a Scoped

    type TagTyped a
    type TagTyped a = Tag a Kinded

data Tagged :: (Pass -> *) -> Pass -> * where
    T :: AST a => { tag :: Tag a π, unTag :: a π } -> Tagged a π

deriving instance (AST a, Show (Tag a π), Show (a π)) => Show (Tagged a π)

newtype Id = Id{ idHash :: Int }
           deriving (Eq, Ord, Enum, Show)

data Ref (π :: Pass) where
    NameRef :: UnscopedPass π => { refName :: String } -> Ref π
    IdRef :: ScopedPass π => {refName :: String, refID ::  Id } -> Ref π
deriving instance Show (Ref π)

instance Eq (Ref π) where
    (NameRef name) == (NameRef name') = name == name'
    (IdRef _ x) == (IdRef _ x') = x == x'

instance Ord (Ref π) where
    (NameRef name) `compare` (NameRef name') = name `compare` name'
    (IdRef _ x) `compare` (IdRef _ x') = x `compare` x'

type Kv = Id

data InOut = In | Out

data Kind (a :: InOut) where
    KStar :: Kind a
    KArr :: Kind a -> Kind a -> Kind a
    KVar :: Kv -> Kind In

instance UVar Kv where
    type UTerm Kv = Kind In

    κ `isVar` α = case κ of
        KVar β -> β == α
        _ -> False

instance HasUVars (Kind In) Kv where
    uvars = execWriter . go
      where
        collect :: Kv -> Writer (Set Kv) ()
        collect = tell . Set.singleton

        go :: Kind In -> Writer (Set Kv) ()
        go κ = case κ of
            KVar α -> collect α
            KArr κ κ' -> go κ >> go κ'
            _ -> return ()

instance SubstUVars (Kind In) Kv where
    θ ▷ κ = case κ of
        KStar -> κ
        KArr κ κ' -> KArr (θ ▷ κ) (θ ▷ κ')
        KVar α -> KVar α `fromMaybe` resolve α θ

data Tv (π :: Pass) where
    TvNamed :: Ref π -> Tv π
    TvFresh :: Id -> Tv Typed
deriving instance Show (Tv π)
deriving instance Eq (Tv π)
deriving instance Ord (Tv π)

type TyCon = Ref

data Ty π = TyCon (TyCon π)
          | TyVar (Tv π)
          | TyApp (Tagged Ty π) (Tagged Ty π)
          | TyFun
deriving instance Show (Tag Ty π) => Show (Ty π)

instance UVar (Tv π) where
    type UTerm (Tv π) = Tagged Ty π

    tτ `isVar` α = case unTag tτ of
        TyVar β -> β == α
        _ -> False

instance HasUVars (Ty π) (Tv π) where
    uvars = execWriter . go
      where
        collect = tell . Set.singleton

        go τ = case τ of
            TyVar α -> collect α
            TyApp t u -> go (unTag t) >> go (unTag u)
            _ -> return ()

instance HasUVars (Tagged Ty π) (Tv π) where
    uvars = uvars . unTag

instance SubstUVars (Tagged Ty Typed) (Tv Typed) where
    θ ▷ tτ = case unTag tτ of
        TyCon con -> tτ
        TyVar α -> tτ `fromMaybe` resolve α θ
        TyApp tt tu -> T (tag tτ) $ TyApp (θ ▷ tt) (θ ▷ tu)
        TyFun -> tτ

tyFunResult :: Tagged Ty π -> Tagged Ty π
tyFunResult (T _ (TyApp (T _ (TyApp (T _ TyFun) _)) lt)) = tyFunResult lt
tyFunResult lt = lt

type Var = Ref

type Con = Ref

class UnscopedPass (π :: Pass)
class ScopedPass (π :: Pass)

instance UnscopedPass Parsed
instance ScopedPass Scoped
instance ScopedPass Kinded
instance ScopedPass Typed

data Defs π where
    DefsUngrouped :: UnscopedPass π => [Tagged Def π] -> Defs π
    DefsGrouped :: ScopedPass π => [[Tagged Def π]] -> Defs π
deriving instance (Show (Tag Def π), Show (Tag Expr π), Show (Tag Match π), Show (Tag Pat π)) => Show (Defs π)

instance SubstUVars (Defs Typed) (Tv Typed) where
    θ ▷ (DefsGrouped defss) = DefsGrouped (θ ▷ defss)

data Def π = DefVar (Var π) (Defs π) (Tagged Expr π)
           | DefFun (Var π) [Tagged Match π]
deriving instance (Show (Defs π), Show (Tag Def π), Show (Tag Expr π), Show (Tag Pat π), Show (Tag Match π)) => Show (Def π)

instance SubstUVars (Def Typed) (Tv Typed) where
    θ ▷ def = case def of
        DefVar var locals body -> DefVar var (θ ▷ locals) (θ ▷ body)
        DefFun fun matches -> DefFun fun (θ ▷ matches)

instance SubstUVars (Tagged Def Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) def) = T (loc, θ ▷ τ) $ θ ▷ def

defName :: Def π -> Var π
defName (DefVar x _ _) = x
defName (DefFun fun _) = fun

data Match π = Match [Tagged Pat π] (Defs π) (Tagged Expr π)
deriving instance (Show (Tag Match π), Show (Tag Pat π), Show (Tag Expr π), Show (Defs π), Show (Tag Def π)) => Show (Match π)

instance SubstUVars (Match Typed) (Tv Typed) where
    θ ▷ Match pats locals body = Match (θ ▷ pats) (θ ▷ locals) (θ ▷ body)

instance SubstUVars (Tagged Match Typed) (Tv Typed) where
    θ ▷ (T loc def) = T loc $ θ ▷ def

data Pat π = PVar (Var π)
           | PCon (Con π) [Tagged Pat π]
           | PWildcard
deriving instance Show (Tag Pat π) => Show (Pat π)

instance SubstUVars (Pat Typed) (Tv Typed) where
    θ ▷ pat = case pat of
        PVar _ -> pat
        PCon con pats -> PCon con (θ ▷ pats)
        PWildcard -> pat

instance SubstUVars (Tagged Pat Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) pat) = T (loc, θ ▷ τ) (θ ▷ pat)

data Expr π = EVar (Var π)
            | ECon (Con π)
            | ELam (Tagged Pat π) (Tagged Expr π)
            | EApp (Tagged Expr π) (Tagged Expr π)
            | ELet (Defs π) (Tagged Expr π)
deriving instance (Show (Tag Expr π), Show (Tag Pat π), Show (Defs π), Show (Tag Def π), Show (Tag Match π)) => Show (Expr π)

instance SubstUVars (Expr Typed) (Tv Typed) where
    θ ▷ e = case e of
        EVar _ -> e
        ECon _ -> e
        ELam pat body -> ELam (θ ▷ pat) (θ ▷ body)
        EApp f x -> EApp (θ ▷ f) (θ ▷ x)
        ELet defs body -> ELet (θ ▷ defs) (θ ▷ body)

instance SubstUVars (Tagged Expr Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) e) = T (loc, θ ▷ τ) (θ ▷ e)

noPos :: SourcePos
noPos = initialPos ""

instance AST Ty where
    type TagKinded Ty = (Maybe (Tag Ty Scoped), Kind Out)

instance AST Def where
    type TagTyped Def = (Tag Def Kinded, Tagged Ty Typed)

instance AST Match

instance AST Pat where
    type TagTyped Pat = (Tag Pat Kinded, Tagged Ty Typed)

instance AST Expr where
    type TagTyped Expr = (Tag Expr Kinded, Tagged Ty Typed)

infixr ~>
(~>) :: Default (Tag Ty π) => Ty π -> Ty π -> Ty π
t ~> u = TyApp (T def $ TyApp (T def $ TyFun) (T def t)) (T def u)

infixr ~~>
(~~>) :: Default (Tag Ty π) => Tagged Ty π -> Tagged Ty π -> Tagged Ty π
t ~~> u = T def $ TyApp (T def $ TyApp (T def $ TyFun) t) u

infixl @@
(@@) :: Default (Tag Expr π) => Expr π -> Expr π -> Expr π
f @@ x = T def f `EApp` T def x
