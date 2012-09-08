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

import Text.PrettyPrint.Leijen hiding ((<$>))
import Mifula.Unify.UVar

import Control.Applicative
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

instance Pretty (Ref π) where
    pretty ref = case ref of
        NameRef s -> text s
        IdRef s _ -> text s

instance Pretty (Ty π) where
    pretty τ = evalState (go 0 τ) (mempty, niceNames)
      where
        tvNames :: Set String
        tvNames = Set.fromList . mapMaybe nameOf . Set.toList $ uvars τ
          where
            nameOf (TvNamed ref) = Just $ refName ref
            nameOf (TvFresh _) = Nothing

        prepend :: [a] -> Stream a -> Stream a
        prepend (x:xs) ys = Cons x $ prepend xs ys
        prepend [] ys = ys

        niceNames :: Stream String
        niceNames = Stream.filter unused $ prepend preferred failsafe
          where
            preferred = ["α", "β", "γ"] ++ map (:[]) ['a'..'z']
            failsafe = fmap (\i -> 't':show i) $ Stream.iterate succ 1
            unused = not . (`Set.member` tvNames)

        niceName :: Id -> State (Map Id String, Stream String) String
        niceName x = do
            mapping <- gets fst
            case Map.lookup x mapping of
                Just s -> return s
                Nothing -> do
                    (Cons s ss) <- gets snd
                    let mapping' = Map.insert x s mapping
                    put (mapping', ss)
                    return s

        goT :: Int -> Tagged Ty π -> State (Map Id String, Stream String) Doc
        goT prec = go prec . unTag

        go :: Int -> Ty π -> State (Map Id String, Stream String) Doc
        go prec ty = case ty of
            TyCon con ->
                return $ pretty con
            TyVar α ->
                case α of
                    TvNamed ref -> return $ pretty ref
                    TvFresh id -> text <$> niceName id
            TyApp (T _ (TyApp (T _ TyFun) t)) u ->
                paren arr_prec <$> (arr <$> goT (arr_prec + 1) t <*> goT 0 u)
            TyApp t u ->
                paren app_prec <$> ((<+>) <$> goT 0 t <*> goT (app_prec + 1) u)
            TyFun ->
                return $ text "(→)"
          where
            app_prec = 10
            arr_prec = 5
            paren lim = if prec > lim then parens else id
            arr f x = f <+> text "→" <+> x

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
