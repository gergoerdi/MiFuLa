{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Mifula.Syntax
       ( Pass(..), AST(..), Tagged(..)
       , Id, Ref(..), Tv, Var, Con, TyCon
       , Ty(..), Expr(..), Pat(..), Match(..), Def(..), Defs(..)
       , defName
       , SourcePos, noPos
       ) where

import Data.Default
import Text.Show
import Text.PrettyPrint.Leijen
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)

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
    type TagTyped a = Maybe SourcePos -- TODO

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

instance Pretty (Ref π) where
    pretty ref = case ref of
        NameRef s -> text s
        IdRef s _ -> text s

type Tv = Ref
type TyCon = Ref

data Ty π = TyCon (TyCon π)
          | TyVar (Tv π)
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
            TyCon con -> pretty con
            TyVar α -> pretty α
            TyApp (T _ (TyApp (T _ TyFun) t)) u ->
                paren arr_prec $ goT (arr_prec + 1) t <+> text "→" <+> goT 0 u
            TyApp t u -> paren app_prec $ goT 0 t <+> goT (app_prec + 1) u
            TyFun -> text "(→)"
          where
            app_prec = 10
            arr_prec = 5
            paren lim = if prec > lim then parens else id

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

instance ( Show (Tag Def π)
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
        DefsUngrouped defs -> join . map pretty $ defs
        DefsGrouped defss -> join . map (vcat . map pretty) $ defss
      where
        sep = line <> text "--------"
        join = vcat . punctuate sep

data Def π = DefVar (Var π) (Defs π) (Tagged Expr π)
           | DefFun (Var π) [Tagged Match π]

defName :: Def π -> Var π
defName (DefVar x _ _) = x
defName (DefFun fun _) = fun

instance Pretty (Def π) where
    pretty def = case def of
        DefVar x locals body ->
            pretty x <+> text "=" <+> pretty body
        DefFun fun matches ->
            vsep . map (prettyMatch fun . unTag) $ matches
      where
        prettyMatch fun (Match pats locals body) =
            hsep [ pretty fun
                 , hsep (map pretty pats)
                 , text "="
                 , pretty body
                 ]

instance ( Show (Defs π)
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

data Match π = Match [Tagged Pat π] (Defs π) (Tagged Expr π)

instance ( Show (Tag Match π)
         , Show (Tag Pat π)
         , Show (Tag Expr π)
         , Show (Defs π)
         , Show (Tag Def π)
         ) => Show (Match π) where
    showsPrec prec match = showParen (prec > 10) $ case match of
        Match pats defs expr ->
            showString "Match " .
            showsPrec 11 pats . showString " " .
            showsPrec 11 defs . showString " " .
            showsPrec 11 expr

data Pat π = PVar (Var π)
           | PCon (Con π) [Tagged Pat π]
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
            pretty x
        PCon con [] ->
            pretty con
        PCon con ps ->
            parens $ pretty con <+> hsep (map pretty ps)
        PWildcard ->
            text "_"

data Expr π = EVar (Var π)
            | ECon (Con π)
            | ELam (Tagged Pat π) (Tagged Expr π)
            | EApp (Tagged Expr π) (Tagged Expr π)
            | ELet (Defs π) (Tagged Expr π)

instance ( Show (Tag Expr π)
         , Show (Tag Pat π)
         , Show (Defs π)
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
                pretty var
            ECon con ->
                pretty con
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

noPos :: SourcePos
noPos = initialPos ""

instance AST Ty
instance AST Def
instance AST Match
instance AST Pat
instance AST Expr

infixr ~>
(~>) :: Default (Tag Ty π) => Ty π -> Ty π -> Ty π
t ~> u = TyApp (T def $ TyApp (T def $ TyFun) (T def t)) (T def u)

infixr ~~>
(~~>) :: Default (Tag Ty π) => Tagged Ty π -> Tagged Ty π -> Tagged Ty π
t ~~> u = T def $ TyApp (T def $ TyApp (T def $ TyFun) t) u

infixl @@
(@@) :: Default (Tag Expr π) => Expr π -> Expr π -> Expr π
f @@ x = T def f `EApp` T def x
