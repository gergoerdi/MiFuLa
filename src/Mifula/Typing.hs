{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Mifula.Typing where

import Mifula.Typing.TC
import Mifula.Unify.UVar
import Mifula.Unify.UEq
import Mifula.Unify
import Mifula.Syntax

import Control.Applicative
import Mifula.Fresh
import Data.Monoid
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Foldable (foldlM)

import Data.Set (Set)
import qualified Data.Set as Set

instantiate :: (HasUVars a (Tv Typed), SubstUVars a (Tv Typed)) => a -> TC a
instantiate x = do
    θ <- foldlM generalize mempty $ uvars x
    return $ θ ▷ x
  where
    generalize θ α = fromMaybe (error "impossible: fresh variable occurs in type") <$>
                     (contract α <$> freshTy <*> pure θ)

ref :: Ref Scoped -> Ref Typed
ref (IdRef name x) = IdRef name x

inferExpr :: Tagged Expr Scoped -> TC (Tagged Expr Typed, Typing)
inferExpr expr = do
    (expr', typing@(τ :@ m)) <- inferExpr_ expr
    return (T (tag expr, τ) expr', typing)

freshTy :: TC (Tagged Ty Typed)
freshTy = T (Nothing, KStar) . TyVar <$> fresh

type TySubst = Subst (Tv Typed)
type TyEq = UEq (Tagged Ty Typed)

unify :: [MonoEnv] -> [Tagged Ty Typed] -> TC (TySubst, MonoEnv, Tagged Ty Typed)
unify ms τs = do
    α <- freshTy
    let eqs = map (:~: α) τs
        eqs' = concatMap toEqs . Set.toList $ vars
    θ <- case unifyEqs True eqs' of
        Left (eq, err) -> do
            undefined -- emit recoverable error
            return mempty
        Right θ -> return θ
    return (θ, θ ▷ mconcat ms, θ ▷ α)
  where
    vars :: Set (Var Scoped)
    vars = mconcat $ map monoVars ms

    toEqs :: Var Scoped -> [TyEq]
    toEqs v = case mapMaybe (lookupMonoVar v) ms of
        [] -> []
        τ:τs -> map (τ :~:) τs

tyArr :: SourcePos -> Tagged Ty Typed -> Tagged Ty Typed -> Tagged Ty Typed
tyArr loc t u = tag KStar $ TyApp (tag (KStar `KArr` KStar) $ TyApp fun t) u
  where
    tag :: Kind Out -> Ty Typed -> Tagged Ty Typed
    tag k = T (Just loc, k)

    fun = tag (KStar `KArr` KStar `KArr` KStar) TyFun

inferExpr_ :: Tagged Expr Scoped -> TC (Expr Typed, Typing)
inferExpr_ (T loc expr) = case expr of
    EVar x -> do
        typing <- do
            mtyping <- lookupPolyVar x
            case mtyping of
                Nothing -> do
                    α <- freshTy
                    return $ monoVar x α
                Just typing -> instantiate typing
        return (EVar (ref x), typing)
    ECon c -> do
        τ <- lookupCon c
        let typing = τ :@ mempty
        typing' <- instantiate typing
        return (ECon (ref c), typing')
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
        (pats', typings') <- unzip <$> mapM inferPat pats
        let ms = map (\(τ :@ m) -> m) typings'
            τs = map (\(τ :@ m) -> τ) typings' -- TODO: unzip...
        (θ, m, _) <- unify ms [τ, foldr (tyArr loc) α τs]
        let τ' = θ ▷ τ
        case τ' of
            (T _ (TyApp (T _ (TyApp (T _ TyFun) _)) _)) -> undefined -- TODO: unsaturated constructor in pattern
            _ -> return ()
        return (T (loc, τ') (θ ▷ PCon (ref con) pats'), τ' :@ m)
    PWildcard -> do
        α <- freshTy
        return (T (loc, α) PWildcard, α :@ mempty)
