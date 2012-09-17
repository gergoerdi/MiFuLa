{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Mifula.Typing (inferDefs) where

import Mifula.Typing.MonoEnv
import Mifula.Typing.PolyEnv
import Mifula.Typing.TC
import Mifula.Unify.UVar
import Mifula.Unify.UEq
import Mifula.Unify
import Mifula.Syntax

import Control.Applicative
import Mifula.Fresh
import Data.Monoid
import Data.Maybe (mapMaybe)
import Data.Foldable (foldlM)

import Data.Set (Set)
import qualified Data.Set as Set

instantiate :: (HasUVars a (Tv Typed), SubstUVars a (Tv Typed)) => a -> TC a
instantiate x = do
    θ <- foldlM generalize mempty $ uvars x
    return $ θ ▷ x
  where
    generalize θ α =
        contract α <$> freshTy <*> pure θ >>=
        maybe (internalError "fresh variable occurs in type") return

ref :: Ref Scoped -> Ref Typed
ref (IdRef name x) = IdRef name x

inferDefs :: Defs Scoped -> TC (Defs Typed)
inferDefs (DefsGrouped defss) = DefsGrouped <$> mapM inferDefGroup defss

inferDefGroup :: [Tagged Def Scoped] -> TC ([Tagged Def Typed])
inferDefGroup = undefined

inferExpr :: Tagged Expr Scoped -> TC (Tagged Expr Typed, Typing)
inferExpr expr = do
    (expr', tyg@(τ :@ m)) <- inferExpr_ expr
    return (T (tag expr, τ) expr', tyg)

freshTy :: TC (Tagged Ty Typed)
freshTy = T (Nothing, KStar) . TyVar <$> fresh

type TySubst = Subst (Tv Typed)
type TyEq = UEq (Tagged Ty Typed)

runUnify :: Bool -> [TyEq] -> TC TySubst
runUnify allowFlip eqs = do
    case unifyEqs True eqs of
        Left (eq, err) -> do
            undefined -- emit recoverable error
            return mempty
        Right θ -> return θ

unify :: [MonoEnv] -> [Tagged Ty Typed] -> TC (TySubst, MonoEnv, Tagged Ty Typed)
unify ms τs = do
    α <- freshTy
    let tyEqs = map (:~: α) τs
    θ <- runUnify True (tyEqs ++ varEqs)
    return (θ, θ ▷ mconcat ms, θ ▷ α)
  where
    varEqs :: [TyEq]
    varEqs = concatMap toEqs . Set.toList $ vars
      where
        toEqs :: Var Scoped -> [TyEq]
        toEqs v = case mapMaybe (lookupMonoVar v) ms of
            [] -> []
            τ:τs -> map (τ :~:) τs

    vars :: Set (Var Scoped)
    vars = mconcat . map monoVars $ ms

unifyPoly :: [PolyEnv] -> TC (TySubst, PolyEnv)
unifyPoly envs = do
    θ <- runUnify True eqs
    let env = mconcat envs
        env' = generalize vars env
    return (θ, θ ▷ env')
  where
    vars :: Set (Var Scoped)
    vars = mconcat . map polyVars $ envs

    eqs :: [TyEq]
    eqs = undefined

tyArr :: SourcePos -> Tagged Ty Typed -> Tagged Ty Typed -> Tagged Ty Typed
tyArr loc t u = tag KStar $ TyApp (tag (KStar `KArr` KStar) $ TyApp fun t) u
  where
    tag :: Kind Out -> Ty Typed -> Tagged Ty Typed
    tag k = T (Just loc, k)

    fun = tag (KStar `KArr` KStar `KArr` KStar) TyFun

inferExpr_ :: Tagged Expr Scoped -> TC (Expr Typed, Typing)
inferExpr_ (T loc expr) = case expr of
    EVar x -> do
        tyg <- do
            mtyg <- lookupPolyVar x
            case mtyg of
                Nothing -> do
                    α <- freshTy
                    return $ monoVar x α
                Just tyg -> instantiate tyg
        return (EVar (ref x), tyg)
    ECon c -> do
        τ <- lookupCon c
        let tyg = τ :@ mempty
        tyg' <- instantiate tyg
        return (ECon (ref c), tyg')
    EApp f arg -> do
        (f', τ₁ :@ m₁) <- inferExpr f
        (arg', τ₂ :@ m₂) <- inferExpr arg
        α <- freshTy
        (θ, m, _) <- unify [m₁, m₂] [τ₁, tyArr loc τ₂ α]
        return (EApp (θ ▷ f') (θ ▷ arg'), (θ ▷ α) :@ m)
    ELam pat body -> do
        (pat', τPat :@ mPat) <- inferPat pat
        (body', τBody :@ mBody) <- inferExpr body
        (θ, m, τ) <- unify [mPat, mBody] [tyArr loc τPat τBody]
        let m' = removeMonoVars (monoVars mPat) m
        return (ELam (θ ▷ pat') (θ ▷ body'), τ :@ m')
    ELet defs body -> do
        defs' <- undefined
        (body', τBody :@ mBody) <- inferExpr body
        (θ, τ :@ m) <- undefined
        return (ELet (θ ▷ defs') (θ ▷ body'), τ :@ m)

inferPat :: Tagged Pat Scoped -> TC (Tagged Pat Typed, Typing)
inferPat (T loc pat) = case pat of
    PVar x -> do
        α <- freshTy
        return (T (loc, α) $ PVar (ref x), monoVar x α)
    PCon con pats -> do
        α <- freshTy
        τ <- instantiate =<< lookupCon con
        (pats', tygs') <- unzip <$> mapM inferPat pats
        let ms = map (\(τ :@ m) -> m) tygs'
            τs = map (\(τ :@ m) -> τ) tygs' -- TODO: unzip...
        (θ, m, _) <- unify ms [τ, foldr (tyArr loc) α τs]
        let τ' = θ ▷ α
        case τ' of
            (T _ (TyApp (T _ (TyApp (T _ TyFun) _)) _)) -> undefined -- TODO: unsaturated constructor in pattern
            _ -> return ()
        return (T (loc, τ') (θ ▷ PCon (ref con) pats'), τ' :@ m)
    PWildcard -> do
        α <- freshTy
        return (T (loc, α) PWildcard, α :@ mempty)
