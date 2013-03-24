{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Mifula.Syntax
       ( Pass(..), ScopedPass
       , AST(..), Tagged(..)
       , Id, PrimId(..), Binding(..), Namespace(..)
       , Ref(..), Var, Con, TyCon, Class
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
    PrimNum :: PrimId NSClass

deriving instance Show (PrimId ns)
deriving instance Eq (PrimId ns)
deriving instance Ord (PrimId ns)

data Namespace = NSVar | NSCon | NSTv | NSTyCon | NSClass
               deriving (Eq, Show)

type Var = Ref NSVar
type Con = Ref NSCon
type TyCon = Ref NSTyCon
type Class = Ref NSClass

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

instance (Monad m) => SubstUVars m (Kind In) Kv where
    θ ▷ κ = case κ of
        KStar -> return κ
        KArr κ κ' -> liftM2 KArr (θ ▷ κ) (θ ▷ κ')
        KVar α -> liftM (fromMaybe $ KVar α) $ resolve α θ

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

instance HasUVars (Tv π) (Tv π) where
    uvars = Set.singleton

instance HasUVars (Ty π) (Tv π) where
    uvars = execWriter . go
      where
        collect = tell . uvars

        go τ = case τ of
            TyVar α -> collect α
            TyApp t u -> go (unTag t) >> go (unTag u)
            _ -> return ()

instance HasUVars (Tagged Ty π) (Tv π) where
    uvars = uvars . unTag

instance (Monad m) => SubstUVars m (Tagged Ty (Kinded In)) Kv where
    θ ▷ (T (mloc, κ) τ) = do
        κ' <- θ ▷ κ
        τ' <- θ ▷ τ
        return $ T (mloc, κ') τ'

instance (Monad m) => SubstUVars m (Ty (Kinded In)) Kv where
    θ ▷ τ = case τ of
        TyApp t u -> liftM2 TyApp (θ ▷ t) (θ ▷ u)
        _ -> return τ

instance (Monad m) => SubstUVars m (Tagged Ty Typed) (Tv Typed) where
    θ ▷ tτ = case unTag tτ of
        TyCon con -> return tτ
        TyVar α -> liftM (fromMaybe tτ) $ resolve α θ
        TyApp tt tu -> liftM (T (tag tτ)) $ liftM2 TyApp (θ ▷ tt) (θ ▷ tu)
        TyFun -> return tτ

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

instance (Monad m) => SubstUVars m (Tagged TyDef (Kinded In)) Kv where
    θ ▷ (T (mloc, κ) td) = do
        κ' <- θ ▷ κ
        td' <- θ ▷ td
        return $ T (mloc, κ') td'

instance (Monad m) => SubstUVars m (TyDef (Kinded In)) Kv where
    θ ▷ td = case td of
        TDAlias name tvs τ -> liftM (TDAlias name tvs) (θ ▷ τ)
        TDData name tvs cons -> liftM (TDData name tvs) (θ ▷ cons)

data ConDef π = ConDef (ConB π) [Tagged Ty π]
deriving instance (Show (Tag Ty π)) => Show (ConDef π)

instance (Monad m) => SubstUVars m (Tagged ConDef (Kinded In)) Kv where
    θ ▷ (T (loc, τ) con) = do
        τ' <- θ ▷ τ
        con' <- θ ▷ con
        return $ T (loc, τ') con'

instance (Monad m) => SubstUVars m (ConDef (Kinded In)) Kv where
    θ ▷ (ConDef name τs) = liftM (ConDef name) $ θ ▷ τs

instance (Monad m) => SubstUVars m (Defs Typed) (Tv Typed) where
    θ ▷ (DefsGrouped defss) = liftM DefsGrouped (θ ▷ defss)

data Def π = DefVar (VarB π) (Defs π) (Tagged Expr π)
           | DefFun (VarB π) [Tagged Match π]
deriving instance (Show (Defs π), Show (Tag Def π), Show (Tag Expr π), Show (Tag Pat π), Show (Tag Match π)) => Show (Def π)

instance (Monad m) => SubstUVars m (Def Typed) (Tv Typed) where
    θ ▷ def = case def of
        DefVar var locals body -> liftM2 (DefVar var) (θ ▷ locals) (θ ▷ body)
        DefFun fun matches -> liftM (DefFun fun) (θ ▷ matches)

instance (Monad m) => SubstUVars m (Tagged Def Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) def) = do
        τ' <- θ ▷ τ
        def' <- θ ▷ def
        return $ T (loc, τ') def'

defName :: Def π -> VarB π
defName (DefVar x _ _) = x
defName (DefFun fun _) = fun

data Match π = Match [Tagged Pat π] (Defs π) (Tagged Expr π)
deriving instance (Show (Tag Match π), Show (Tag Pat π), Show (Tag Expr π), Show (Defs π), Show (Tag Def π)) => Show (Match π)

instance (Monad m) => SubstUVars m (Match Typed) (Tv Typed) where
    θ ▷ Match pats locals body = liftM3 Match (θ ▷ pats) (θ ▷ locals) (θ ▷ body)

instance (Monad m) => SubstUVars m (Tagged Match Typed) (Tv Typed) where
    θ ▷ (T loc def) = liftM (T loc) (θ ▷ def)

data Pat π = PVar (VarB π)
           | PCon (Con π) [Tagged Pat π]
           | PWildcard
deriving instance Show (Tag Pat π) => Show (Pat π)

instance (Monad m) => SubstUVars m (Pat Typed) (Tv Typed) where
    θ ▷ pat = case pat of
        PVar _ -> return pat
        PCon con pats -> liftM (PCon con) (θ ▷ pats)
        PWildcard -> return pat

instance (Monad m) => SubstUVars m (Tagged Pat Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) pat) = do
        τ' <- θ ▷ τ
        pat' <- θ ▷ pat
        return $ T (loc, τ') pat'

data Lit = LInt Integer
         deriving Show

data Expr π = EVar (Var π)
            | ECon (Con π)
            | ELit Lit
            | ELam (Tagged Pat π) (Tagged Expr π)
            | EApp (Tagged Expr π) (Tagged Expr π)
            | ELet (Defs π) (Tagged Expr π)
deriving instance (Show (Tag Expr π), Show (Tag Pat π), Show (Defs π), Show (Tag Def π), Show (Tag Match π)) => Show (Expr π)

instance (Monad m) => SubstUVars m (Expr Typed) (Tv Typed) where
    θ ▷ e = case e of
        EVar _ -> return e
        ECon _ -> return e
        ELit _ -> return e
        ELam pat body -> liftM2 ELam (θ ▷ pat) (θ ▷ body)
        EApp f x -> liftM2 EApp (θ ▷ f) (θ ▷ x)
        ELet defs body -> liftM2 ELet (θ ▷ defs) (θ ▷ body)

instance (Monad m) => SubstUVars m (Tagged Expr Typed) (Tv Typed) where
    θ ▷ (T (loc, τ) e) = do
        τ' <- θ ▷ τ
        e' <- θ ▷ e
        return $ T (loc, τ') e'

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
