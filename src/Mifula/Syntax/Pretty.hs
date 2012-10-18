{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Mifula.Syntax.Pretty () where

import Mifula.Syntax
import Mifula.Prims
import Mifula.Syntax.Readable

import Text.PrettyPrint.Leijen hiding ((<$>))
import Mifula.Unify.UVar

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Writer hiding ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream

instance Pretty (a π) => Pretty (Tagged a π) where
    pretty = pretty . unTag

instance Pretty (Binding ns π) where
    pretty = text . bindName

instance (Prim ns) => Pretty (Ref ns π) where
    pretty ref = case ref of
        PrimRef p -> text $ desolvePrim p
        BindingRef b -> pretty b

-- We can only pretty-print types that don't contain generated type
-- variables.
type family HasFreshTvs (π :: Pass) :: Bool
type instance HasFreshTvs Parsed = False
type instance HasFreshTvs Scoped = False
type instance HasFreshTvs (Kinded dir) = False
type instance HasFreshTvs Typed = True

instance (HasFreshTvs π ~ False) => Pretty (Ty π) where
    pretty = go 0
      where
        goT prec = go prec . unTag

        go prec ty = case ty of
            TyCon con ->
                pretty con
            TyVar (TvNamed ref) ->
                pretty ref
            TyApp (T _ (TyApp (T _ TyFun) t)) u ->
                paren arr_prec $ t ~> u
            TyApp t u ->
                paren app_prec $ goT 0 t <+> goT (app_prec + 1) u
            TyFun ->
                text "(→)"
          where
            app_prec = 10
            arr_prec = 5
            paren lim = if prec > lim then parens else id
            arr f x = f <+> text "→" <+> x
            t ~> u = arr (goT (arr_prec + 1) t) (goT 0 u)

instance Pretty (Defs π) where
    pretty defs = case defs of
        DefsUngrouped defs -> join . map pretty $ defs
        DefsGrouped defss -> join . map (vcat . map pretty) $ defss
      where
        sep = line <> text "--------"
        join = vcat . punctuate sep

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

instance Pretty Lit where
    pretty lit = case lit of
        LInt n -> pretty n

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
            ELit lit -> pretty lit
            ELet defs body ->
                error "TODO: pretty-print ELet"
          where
            app_prec = 10
            lam_prec = 5
            paren lim = if prec > lim then parens else id

instance Pretty (TyDef Parsed) where
    pretty tydef = case tydef of
        TDAlias name formals τ ->
            text "type" <+> pretty name <+> hsep (map pretty formals)
            <+> equals <+> pretty τ
        TDData name formals cons ->
            text "data" <+> pretty name <+> hsep (map pretty formals)
            <+> enclose (map pretty cons)
      where
        enclose = encloseSep (equals <+> empty) empty (text "| ")

instance Pretty (ConDef Parsed) where
    pretty (ConDef con args) = pretty con <+> hsep (map pretty args)

instance Pretty Decl where
    pretty decl = case decl of
        DeclDef def -> pretty def
        DeclTyDef tydef -> pretty tydef
