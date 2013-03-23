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
import Mifula.Prims

import Control.Applicative
import Mifula.Fresh
import Data.Monoid
import Data.Maybe (mapMaybe)
import Data.Foldable (foldlM)

import Data.Set (Set)
import qualified Data.Set as Set

instantiate :: (HasUVars a (Tv Typed), SubstUVars TC a (Tv Typed)) => a -> TC a
instantiate x = do
    θ <- foldlM generalize mempty $ uvars x
    θ ▷ x
  where
    generalize :: Subst (Tv Typed) -> Tv Typed -> TC (Subst (Tv Typed))
    generalize θ α =
        contract α <$> freshTy <*> pure θ >>=
        maybe (internalError "fresh variable occurs in type") return

ref :: Ref ns (Kinded Out) -> Ref ns Typed
ref (BindingRef b) = BindingRef $ bind b
ref (PrimRef prim) = PrimRef prim

bind :: Binding ns (Kinded Out) -> Binding ns Typed
bind (BindId name x) = BindId name x

inferDefs :: Defs (Kinded Out) -> TC (Defs Typed, PolyEnv)
inferDefs (DefsGrouped defss) = do
    -- TODO: fold envs
    (defss', envs) <- go defss
    return (DefsGrouped defss', mconcat envs)
  where
    go (defs:defss) = do
        (defs', env) <- inferDefGroup defs
        (defss', envs) <- withEnv env $ go defss
        return (defs':defss', env:envs)
    go [] = return ([], [])

inferDefGroup :: [Tagged Def (Kinded Out)] -> TC ([Tagged Def Typed], PolyEnv)
inferDefGroup defs = do
    (defs', envs) <- unzip <$> mapM inferDef defs
    (θ, env) <- unifyPoly envs
    defs'' <- θ ▷ defs'
    return (defs'', env)
  where
    inferDef :: Tagged Def (Kinded Out) -> TC (Tagged Def Typed, PolyEnv)
    inferDef (T loc def) = do
        (x, def', tyg@(τ :@ _)) <- inferDef_ def
        return (T (loc, τ) def', polyVar x tyg)

    inferDef_ :: Def (Kinded Out) -> TC (VarB (Kinded Out), Def Typed, Typing)
    inferDef_ def = case def of
        DefVar x locals body -> do
            -- TODO: locals
            let locals' = DefsGrouped []

            (body', τ :@ m) <- inferExpr body
            m' <- removeMonoVars (Set.singleton x) m
            let def' = DefVar (bind x) locals' body'
            return (x, def', τ :@ m')
        DefFun fun matches -> do
            (matches', tygs) <- unzip <$> mapM inferMatch matches
            let (τs, ms) = unzip $ map (\ (τ :@ m) -> (τ, m)) tygs
            (θ, m, τ) <- unify ms τs
            matches'' <- θ ▷ matches'
            return (fun, DefFun (bind fun) matches'', τ :@ m)

    inferMatch :: Tagged Match (Kinded Out) -> TC (Tagged Match Typed, Typing)
    inferMatch (T loc (Match pats locals body)) = do
        (pats', patTygs) <- unzip <$> mapM inferPat pats
        let mPats = map (\(τ :@ m) -> m) patTygs
            τPats = map (\(τ :@ m) -> τ) patTygs

        -- TODO: locals
        let locals' = DefsGrouped []

        (body', τBody :@ mBody) <- inferExpr body
        (θ, m, τ) <- unify (mBody:mPats) [foldr (tyArr loc) τBody τPats]
        m' <- removeMonoVars (Set.unions $ map monoVars mPats) m
        pats'' <- θ ▷ pats'
        locals'' <- θ ▷ locals'
        body'' <- θ ▷ body'
        return (T loc $ Match pats'' locals'' body'', τ :@ m')

inferExpr :: Tagged Expr (Kinded Out) -> TC (Tagged Expr Typed, Typing)
inferExpr expr = do
    (expr', tyg@(τ :@ m)) <- inferExpr_ expr
    return (T (tag expr, τ) expr', tyg)

freshTy :: TC (Tagged Ty Typed)
freshTy = T (Nothing, KStar) . TyVar <$> fresh

type TySubst = Subst (Tv Typed)
type TyEq = UEq (Tagged Ty Typed)

runUnify :: Bool -> [TyEq] -> TC TySubst
runUnify allowFlip eqs = do
    result <- unifyEqs True eqs
    case result of
        Left (eq, err) -> do
            error (show err) -- TODO: emit recoverable error
            return mempty
        Right θ -> return θ

unify :: [MonoEnv] -> [Tagged Ty Typed] -> TC (TySubst, MonoEnv, Tagged Ty Typed)
unify ms τs = do
    α <- freshTy
    let tyEqs = map (:~: α) τs
    θ <- runUnify True (tyEqs ++ varEqs)
    m <- θ ▷ mconcat ms
    τ <- θ ▷ α
    return (θ, m, τ)
  where
    varEqs :: [TyEq]
    varEqs = concatMap toEqs . Set.toList $ vars
      where
        toEqs :: VarB (Kinded Out) -> [TyEq]
        toEqs v = case mapMaybe (lookupMonoVar v) ms of
            [] -> []
            τ:τs -> map (τ :~:) τs

    vars :: Set (VarB (Kinded Out))
    vars = mconcat . map monoVars $ ms

unifyPoly :: [PolyEnv] -> TC (TySubst, PolyEnv)
unifyPoly envs = do
    (θ, _, _) <- unify ms []
    let env = mconcat envs
    env' <- generalize vars env
    env'' <- θ ▷ env'
    return (θ, env'')
  where
    vars :: Set (VarB (Kinded Out))
    vars = mconcat . map polyVars $ envs

    ms :: [MonoEnv]
    ms = concatMap polyMonos envs

tyArr :: SourcePos -> Tagged Ty Typed -> Tagged Ty Typed -> Tagged Ty Typed
tyArr loc t u = tag KStar $ TyApp (tag (KStar `KArr` KStar) $ TyApp fun t) u
  where
    tag :: Kind Out -> Ty Typed -> Tagged Ty Typed
    tag κ = T (Just loc, κ)

    fun = tag (KStar `KArr` KStar `KArr` KStar) TyFun

inferExpr_ :: Tagged Expr (Kinded Out) -> TC (Expr Typed, Typing)
inferExpr_ (T loc expr) = case expr of
    EVar x -> do
        tyg <- case x of
            PrimRef p -> instantiate $ primVarTy p :@ mempty
            BindingRef b -> do
                mtyg <- lookupVar b
                case mtyg of
                    Nothing -> do
                        α <- freshTy
                        return $ monoVar b α
                    Just tyg -> instantiate tyg
        return (EVar (ref x), tyg)
    ECon c -> do
        τ <- lookupCon c
        let tyg = τ :@ mempty
        tyg' <- instantiate tyg
        return (ECon (ref c), tyg')
    ELit lit -> do
        τ <- T (Just loc, KStar) <$> inferLit lit
        let tyg = τ :@ mempty
        return (ELit lit, tyg)
    EApp f arg -> do
        (f', τ₁ :@ m₁) <- inferExpr f
        (arg', τ₂ :@ m₂) <- inferExpr arg
        α <- freshTy
        (θ, m, _) <- unify [m₁, m₂] [τ₁, tyArr loc τ₂ α]
        f'' <- θ ▷ f'
        arg'' <- θ ▷ arg'
        τ <- θ ▷ α
        return (EApp f'' arg'', τ :@ m)
    ELam pat body -> do
        (pat', τPat :@ mPat) <- inferPat pat
        (body', τBody :@ mBody) <- inferExpr body
        (θ, m, τ) <- unify [mPat, mBody] [tyArr loc τPat τBody]
        m' <- removeMonoVars (monoVars mPat) m
        pat'' <- θ ▷ pat'
        body'' <- θ ▷ body'
        return (ELam pat'' body'', τ :@ m')
    ELet defs body -> do
        (defs', env) <- inferDefs defs
        (body', τBody :@ mBody) <- withEnv env $ inferExpr body
        (θ, m, τ) <- unify undefined undefined -- TODO
        defs'' <- θ ▷ defs'
        body'' <- θ ▷ body'
        return (ELet defs'' body'', τ :@ m)

inferPat :: Tagged Pat (Kinded Out) -> TC (Tagged Pat Typed, Typing)
inferPat (T loc pat) = case pat of
    PVar x -> do
        α <- freshTy
        return (T (loc, α) $ PVar (bind x), monoVar x α)
    PCon con pats -> do
        α <- freshTy
        τ <- instantiate =<< lookupCon con
        (pats', tygs') <- unzip <$> mapM inferPat pats
        let ms = map (\(τ :@ m) -> m) tygs'
            τs = map (\(τ :@ m) -> τ) tygs' -- TODO: unzip...
        (θ, m, _) <- unify ms [τ, foldr (tyArr loc) α τs]
        τ' <- θ ▷ α
        case τ' of
            (T _ (TyApp (T _ (TyApp (T _ TyFun) _)) _)) -> undefined -- TODO: unsaturated constructor in pattern
            _ -> return ()
        pat' <- θ ▷ PCon (ref con) pats'
        return (T (loc, τ') pat', τ' :@ m)
    PWildcard -> do
        α <- freshTy
        return (T (loc, α) PWildcard, α :@ mempty)

inferLit :: Lit -> TC (Ty Typed)
inferLit (LInt _) = return $ TyCon $ PrimRef PrimInt
