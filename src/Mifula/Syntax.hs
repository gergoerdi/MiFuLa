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
       , InOut(..), Kind(..)
       , Expr(..), Pat(..)
       , Match(..), Def(..), Defs(..)
       , defName
       , SourcePos, noPos
       ) where

import Data.Default
import Text.Show
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos)
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

type Kv = Id

data InOut = In | Out

data Kind (a :: InOut) where
    KStar :: Kind a
    KArr :: Kind a -> Kind a -> Kind a
    KVar :: Kv -> Kind In

instance UVar (Kind In) Kv where
    injectVar = KVar

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
        KVar α -> resolve α θ

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

instance UVar (Ty π) (Tv π) where
    injectVar = TyVar

    τ `isVar` α = case τ of
        TyVar β -> β == α
        _ -> False

instance (Default (Tag Ty π)) => UVar (Tagged Ty π) (Tv π) where
    injectVar = T def . TyVar

    tτ `isVar` α = unTag tτ `isVar` α

instance HasUVars (Ty π) (Tv π) where
    uvars = execWriter . go
      where
        collect = tell . Set.singleton

        go τ = case τ of
            TyVar α -> collect α
            TyApp t u -> go (unTag t) >> go (unTag u)
            _ -> return ()

instance (Default (Tag Ty π)) => HasUVars (Tagged Ty π) (Tv π) where
    uvars = uvars . unTag

instance SubstUVars (Tagged Ty Typed) (Tv Typed) where
    θ ▷ tτ = case unTag tτ of
        TyCon con -> tτ
        TyVar α -> resolve α θ
        TyApp tt tu -> T (tag tτ) $ TyApp (θ ▷ tt) (θ ▷ tu)
        TyFun -> tτ

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

instance AST Ty where
    type TagKinded Ty = (Tag Ty Scoped, Kind Out)

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
