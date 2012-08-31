{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
module Mifula.Syntax where

import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Writer
import Data.Set.Unicode
import Text.Show

import Data.Default
import Text.PrettyPrint.Leijen

data Pass = Parsed
          | Scoped
          | Typed

class AST (a :: Pass -> *) where
    type Tag a (π :: Pass)
    type Tag a Parsed = TagParsed a
    type Tag a Scoped = TagScoped a
    type Tag a Typed = TagTyped a

    type TagParsed a
    type TagParsed a = SrcLoc

    type TagScoped a
    type TagScoped a = Tag a Parsed

    type TagTyped a
    type TagTyped a = SrcLoc -- TODO

data Tagged :: (Pass -> *) -> Pass -> * where
    T :: AST a => { tag :: Tag a π, unTag :: a π } -> Tagged a π

instance (AST a, Show (Tag a π), Show (a π)) => Show (Tagged a π) where
    showsPrec prec T{..} = showParen (prec > 10) $
                           showString "Tagged " .
                           showsPrec 11 tag .
                           showString " " .
                           showsPrec 11 unTag

instance Pretty (a π) => Pretty (Tagged a π) where
    pretty = pretty . unTag

type Id = String

type Tv = Id
type TyCon = Id

data Ty π = TyCon TyCon
          | TyVar Tv
          | TyApp (Tagged Ty π) (Tagged Ty π)
          | TyFun

tyFunResult :: Tagged Ty π -> Tagged Ty π
tyFunResult (T _ (TyApp (T _ (TyApp (T _ TyFun) _)) lt)) = tyFunResult lt
tyFunResult lt = lt

instance (Show (Tag Ty π)) => Show (Ty π) where
    showsPrec prec ty = case ty of
        TyCon con -> paren $ showString "TyCon " . showsPrec 0 con
        TyVar α -> paren $ showString "TyVar " . showsPrec 0 α
        TyApp tt tu -> paren $
                       showString "TyApp " .
                       showsPrec 11 tt .
                       showString " " .
                       showsPrec 11 tu
        TyFun -> showString "TyFun"
      where
        paren = showParen (prec > 10)

instance Pretty (Ty π) where
    pretty = go 0
      where
        goT :: Int -> Tagged Ty π -> Doc
        goT prec = go prec . unTag

        go :: Int -> Ty π -> Doc
        go prec ty = case ty of
            TyCon con -> text con
            TyVar α -> text α
            TyApp (T _ (TyApp (T _ TyFun) t)) u ->
                paren arr_prec $ goT (arr_prec + 1) t <+> text "→" <+> goT 0 u
            TyApp t u -> paren app_prec $ goT 0 t <+> goT (app_prec + 1) u
            TyFun -> text "(→)"
          where
            app_prec = 10
            arr_prec = 5
            paren lim = if prec > lim then parens else id

type Var = Id

type Con = Id

class UnscopedPass (π :: Pass)
class ScopedPass (π :: Pass)

instance UnscopedPass Parsed
instance ScopedPass Scoped
instance ScopedPass Typed

data Defs π where
    DefsUngrouped :: UnscopedPass π => [Tagged Def π] -> Defs π
    DefsGrouped :: ScopedPass π => [[Tagged Def π]] -> Defs π

instance ( Show (Tag Defs π)
         , Show (Tag Def π)
         , Show (Tag Expr π)
         , Show (Tag Match π)
         , Show (Tag Pat π)
         ) => Show (Defs π) where
    showsPrec prec defs = case defs of
        DefsUngrouped defs ->
            showString "DefsUngrouped " . showsPrec 11 defs
        DefsGrouped defss ->
            showString "DefsGrouped " . showsPrec 11 defss

instance Pretty (Defs π) where
    pretty defs = case defs of
        DefsUngrouped defs -> vcat . map pretty $ defs
        DefsGrouped defss -> vcat . map (vcat . map pretty) $ defss

data Def π = DefVar Var (Tagged Defs π) (Tagged Expr π)
           | DefFun Var [Tagged Match π]

defName :: Def π -> Var
defName (DefVar x _ _) = x
defName (DefFun fun _) = fun

instance Pretty (Def π) where
    pretty def = case def of
        DefVar x locals body ->
            text x <+> text "=" <+> pretty body
        DefFun fun matches ->
            vsep . map (prettyMatch fun . unTag) $ matches
      where
        prettyMatch fun (Match pats locals body) =
            hsep [ text fun
                 , hsep (map pretty pats)
                 , text "="
                 , pretty body
                 ]

instance ( Show (Tag Defs π)
         , Show (Tag Def π)
         , Show (Tag Expr π)
         , Show (Tag Pat π)
         , Show (Tag Match π)
         ) => Show (Def π) where
    showsPrec prec def = case def of
        DefVar var locals expr ->
            showString "DefVar " .
            showsPrec 11 var . showString " " .
            showsPrec 11 locals . showString " " .
            showsPrec 11 expr
        DefFun f matches ->
            showString "DefFun " .
            showsPrec 11 f . showString " " .
            showsPrec 11 matches

data Match π = Match [Tagged Pat π] (Tagged Defs π) (Tagged Expr π)

instance ( Show (Tag Match π)
         , Show (Tag Pat π)
         , Show (Tag Expr π)
         , Show (Tag Defs π)
         , Show (Tag Def π)
         ) => Show (Match π) where
    showsPrec prec match = showParen (prec > 10) $ case match of
        Match pats defs expr ->
            showString "Match " .
            showsPrec 11 pats . showString " " .
            showsPrec 11 defs . showString " " .
            showsPrec 11 expr

data Pat π = PVar Var
           | PCon Con [Tagged Pat π]
           | PWildcard

instance (Show (Tag Pat π)) => Show (Pat π) where
    showsPrec prec pat = case pat of
        PVar x ->
            paren $ showString "PVar " . showsPrec 0 x
        PCon con ps ->
            paren $
            showString "PCon " .
            showsPrec 11 con . showString " " .
            shows ps
        PWildcard ->
            showString "PWildcard"
      where
        paren = showParen (prec > 10)

instance Pretty (Pat π) where
    pretty pat = case pat of
        PVar x ->
            text x
        PCon con [] ->
            text con
        PCon con ps ->
            parens $ text con <+> hsep (map pretty ps)
        PWildcard ->
            text "_"

data Expr π = EVar Var
            | ECon Con
            | ELam (Tagged Pat π) (Tagged Expr π)
            | EApp (Tagged Expr π) (Tagged Expr π)
            | ELet (Tagged Defs π) (Tagged Expr π)

instance ( Show (Tag Expr π)
         , Show (Tag Pat π)
         , Show (Tag Defs π)
         , Show (Tag Def π)
         , Show (Tag Match π)
         ) => Show (Expr π) where
    showsPrec prec e = case e of
        EVar var ->
            paren $ showString "EVar " . showsPrec 0 var
        ECon con ->
            paren $ showString "ECon " . showsPrec 0 con
        ELam pat exp ->
            paren $
            showString "ELam " .
            showsPrec 11 pat .
            showsPrec 11 exp
        EApp f x ->
            paren $
            showString "EApp " .
            showsPrec 11 f .
            showString " " .
            showsPrec 11 x
        ELet defs exp ->
            paren $
            showString "ELet " .
            showsPrec 11 defs .
            showString " " .
            showsPrec 11 exp
      where
        paren = showParen (prec > 10)

instance Pretty (Expr π) where
    pretty = go 0
      where
        goT :: Int -> Tagged Expr π -> Doc
        goT prec = go prec . unTag

        go :: Int -> Expr π -> Doc
        go prec e = case e of
            EVar var ->
                text var
            ECon con ->
                text con
            ELam pat body ->
                paren lam_prec $ text "λ" <+> pretty pat <+> text "→" <+> pretty body
            EApp f x ->
                paren app_prec $ goT app_prec f <+> goT (app_prec + 1) x
            ELet defs body ->
                undefined -- TODO
          where
            app_prec = 10
            lam_prec = 5
            paren lim = if prec > lim then parens else id

data SrcLoc = SrcLoc
            deriving Show

instance Default SrcLoc where
    def = SrcLoc

instance AST Ty
instance AST Defs where
    type TagParsed Defs = ()
    type TagTyped Defs = ()
instance AST Def
instance AST Match
instance AST Pat
instance AST Expr

class HasTypeVars a where
    tvs :: a -> Set Tv

occurs :: (HasTypeVars a) => Tv -> a -> Bool
occurs x ty = x ∈ tvs ty

instance HasTypeVars (Ty π) where
    tvs = execWriter . go
      where
        collect = tell . Set.singleton

        go ty = case ty of
            TyVar tv -> collect tv
            TyApp t u -> go (unTag t) >> go (unTag u)
            _ -> return ()

infixr ~>
(~>) :: Default (Tag Ty π) => Ty π -> Ty π -> Ty π
t ~> u = TyApp (T def $ TyApp (T def $ TyFun) (T def t)) (T def u)

infixr ~~>
(~~>) :: Default (Tag Ty π) => Tagged Ty π -> Tagged Ty π -> Tagged Ty π
t ~~> u = T def $ TyApp (T def $ TyApp (T def $ TyFun) t) u

t :: Tagged Ty Parsed
t = (a ~~> b) ~~> list a ~~> list b
  where
    list = T def . TyApp (T def $ TyCon "List")
    a = T def $ TyVar "a"
    b = T def $ TyVar "b"

infixl @@
(@@) :: Default (Tag Expr π) => Expr π -> Expr π -> Expr π
f @@ x = T def f `EApp` T def x
