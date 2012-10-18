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
       , Id, PrimId(..), Binding(..), Namespace(..)
       , Ref(..), Var, Con, TyCon
       , VarB, ConB, TyConB
       , Ty(..), Tv(..)
       , Kv, InOut(..), Kind(..)
       , Expr(..), Lit(..), Pat(..)
       , Match(..), Def(..), Defs(..)
       , TyDef(..), ConDef(..)
       , Decl(..)
       , defName
       , SourcePos, noPos
       ) where

import Mifula.Id

import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)
import Mifula.Unify.UVar

import Control.Monad.Writer hiding ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

data Pass = Parsed
          | Scoped
          | Kinded InOut
          | Typed

class AST (a :: Pass -> *) where
    type Tag a (π :: Pass)
    type Tag a Parsed = TagParsed a
    type Tag a Scoped = TagScoped a
    type Tag a (Kinded In) = TagKinded In a
    type Tag a (Kinded Out) = TagKinded Out a
    type Tag a Typed = TagTyped a

    type TagParsed a
    type TagParsed a = SourcePos

    type TagScoped a
    type TagScoped a = Tag a Parsed

    type TagKinded (dir :: InOut) a
    type TagKinded In a = Tag a Scoped
    type TagKinded Out a = Tag a (Kinded In)

    type TagTyped a
    type TagTyped a = Tag a (Kinded Out)

data Tagged :: (Pass -> *) -> Pass -> * where
    T :: AST a => { tag :: Tag a π, unTag :: a π } -> Tagged a π
deriving instance (AST a, Show (Tag a π), Show (a π)) => Show (Tagged a π)

data PrimId :: Namespace -> * where
    PrimPlus :: PrimId NSVar
    PrimInt :: PrimId NSTyCon

deriving instance Show (PrimId ns)
deriving instance Eq (PrimId ns)
deriving instance Ord (PrimId ns)

data Namespace = NSVar | NSCon | NSTv | NSTyCon
               deriving (Eq, Show)

type Var = Ref NSVar
type Con = Ref NSCon
type TyCon = Ref NSTyCon

type VarB = Binding NSVar
type ConB = Binding NSCon
type TyConB = Binding NSTyCon

data Binding (ns :: Namespace) (π :: Pass) where
    BindName :: (ScopedPass π ~ False) => { bindName :: String } -> Binding ns π
    BindId :: (ScopedPass π ~ True) => { bindName :: String, bindID :: Id } -> Binding ns π
deriving instance Show (Binding ns π)

instance Eq (Binding ns π) where
    (BindName name) == (BindName name') = name == name'
    (BindId _ x) == (BindId _ x') = x == x'

instance Ord (Binding ns π) where
    (BindName name) `compare` (BindName name') = name `compare` name'
    (BindId _ x) `compare` (BindId _ x') = x `compare` x'

data Ref (ns :: Namespace) (π :: Pass) where
    BindingRef :: Binding ns π -> Ref ns π
    PrimRef :: (ScopedPass π ~ True) => PrimId ns -> Ref ns π
deriving instance Show (Ref ns π)
deriving instance Eq (Ref ns π)

type Kv = Id

data InOut = In | Out

data Kind (dir :: InOut) where
    KStar :: Kind dir
    KArr :: Kind dir -> Kind dir -> Kind dir
    KVar :: Kv -> Kind In
deriving instance Show (Kind dir)

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
    TvNamed :: Binding NSTv π -> Tv π
    TvFresh :: Id -> Tv Typed
deriving instance Show (Tv π)
deriving instance Eq (Tv π)
deriving instance Ord (Tv π)

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

instance SubstUVars (Tagged Ty (Kinded In)) Kv where
    θ ▷ (T (mloc, κ) τ) = T (mloc, θ ▷ κ) $ θ ▷ τ

instance SubstUVars (Ty (Kinded In)) Kv where
    θ ▷ τ = case τ of
        TyApp t u -> TyApp (θ ▷ t) (θ ▷ u)
        _ -> τ

instance SubstUVars (Tagged Ty Typed) (Tv Typed) where
    θ ▷ tτ = case unTag tτ of
        TyCon con -> tτ
        TyVar α -> tτ `fromMaybe` resolve α θ
        TyApp tt tu -> T (tag tτ) $ TyApp (θ ▷ tt) (θ ▷ tu)
        TyFun -> tτ

type family ScopedPass (π :: Pass) :: Bool
type instance ScopedPass Parsed = False
type instance ScopedPass Scoped = True
type instance ScopedPass (Kinded dir) = True
type instance ScopedPass Typed = True

data Decl = DeclDef (Tagged Def Parsed)
          | DeclTyDef (Tagged TyDef Parsed)
          deriving Show

data Defs π where
    DefsUngrouped :: (ScopedPass π ~ False) => [Tagged Def π] -> Defs π
    DefsGrouped :: (ScopedPass π ~ True) => [[Tagged Def π]] -> Defs π
deriving instance (Show (Tag Def π), Show (Tag Expr π), Show (Tag Match π), Show (Tag Pat π)) => Show (Defs π)

data TyDef π = TDAlias (TyConB π) [Binding NSTv π] (Tagged Ty π) -- TODO: tag the type formals?
             | TDData (TyConB π) [Binding NSTv π] [Tagged ConDef π]
deriving instance (Show (Tag Ty π), Show (Tag ConDef π)) => Show (TyDef π)

instance SubstUVars (Tagged TyDef (Kinded In)) Kv where
    θ ▷ (T (mloc, κ) td) = T (mloc, θ ▷ κ) $ θ ▷ td

instance SubstUVars (TyDef (Kinded In)) Kv where
    θ ▷ td = case td of
        TDAlias name tvs τ -> TDAlias name tvs (θ ▷ τ)
        TDData name tvs cons -> TDData name tvs (θ ▷ cons)

data ConDef π = ConDef (ConB π) [Tagged Ty π]
deriving instance (Show (Tag Ty π)) => Show (ConDef π)

instance SubstUVars (Tagged ConDef (Kinded In)) Kv where
    θ ▷ (T (loc, τ) con) = T (loc, θ ▷ τ) (θ ▷ con)

instance SubstUVars (ConDef (Kinded In)) Kv where
    θ ▷ (ConDef name τs) = ConDef name $ θ ▷ τs

instance SubstUVars (Defs Typed) (Tv Typed) where
    θ ▷ (DefsGrouped defss) = DefsGrouped (θ ▷ defss)

data Def π = DefVar (VarB π) (Defs π) (Tagged Expr π)
           | DefFun (VarB π) [Tagged Match π]
deriving instance (Show (Defs π), Show (Tag Def π), Show (Tag Expr π), Show (Tag Pat π), Show (Tag Match π)) => Show (Def π)

instance SubstUVars (Def Typed) (Tv Typed) where
    θ ▷ def = case def of
        DefVar var locals body -> DefVar var (θ ▷ locals) (θ ▷ body)
        DefFun fun matches -> DefFun fun (θ ▷ matches)

instance SubstUVars (Tagged Def Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) def) = T (loc, θ ▷ τ) $ θ ▷ def

defName :: Def π -> VarB π
defName (DefVar x _ _) = x
defName (DefFun fun _) = fun

data Match π = Match [Tagged Pat π] (Defs π) (Tagged Expr π)
deriving instance (Show (Tag Match π), Show (Tag Pat π), Show (Tag Expr π), Show (Defs π), Show (Tag Def π)) => Show (Match π)

instance SubstUVars (Match Typed) (Tv Typed) where
    θ ▷ Match pats locals body = Match (θ ▷ pats) (θ ▷ locals) (θ ▷ body)

instance SubstUVars (Tagged Match Typed) (Tv Typed) where
    θ ▷ (T loc def) = T loc $ θ ▷ def

data Pat π = PVar (VarB π)
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

data Lit = LInt Integer
         deriving Show

data Expr π = EVar (Var π)
            | ECon (Con π)
            | ELit Lit
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

instance AST TyDef where
    type TagKinded In TyDef = (Tag TyDef Scoped, Kind In)
    type TagKinded Out TyDef = (Tag TyDef Scoped, Kind Out)

instance AST ConDef where
    type TagKinded In ConDef = (Tag ConDef Scoped, Tagged Ty (Kinded In))
    type TagKinded Out ConDef = (Tag ConDef Scoped, Tagged Ty (Kinded Out))

instance AST Ty where
    type TagKinded In Ty = (Maybe (Tag Ty Scoped), Kind In)
    type TagKinded Out Ty = (Maybe (Tag Ty Scoped), Kind Out)

instance AST Def where
    type TagTyped Def = (Tag Def (Kinded Out), Tagged Ty Typed)

instance AST Match

instance AST Pat where
    type TagTyped Pat = (Tag Pat (Kinded Out), Tagged Ty Typed)

instance AST Expr where
    type TagTyped Expr = (Tag Expr (Kinded Out), Tagged Ty Typed)
