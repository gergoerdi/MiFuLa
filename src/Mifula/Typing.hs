{-# LANGUAGE DataKinds, GADTs #-}
module Mifula.Typing where

import Mifula.Typing.TC
import Mifula.Unify.UVar
import Mifula.Syntax
import Control.Applicative
import Mifula.Fresh
import Data.Monoid

import Data.Set (Set)
import qualified Data.Set as Set

instantiateTyping :: Typing -> TC Typing
instantiateTyping = undefined

instantiateTy :: Tagged Ty Typed -> TC (Tagged Ty Typed)
instantiateTy = undefined

ref :: Ref Scoped -> Ref Typed
ref (IdRef name x) = IdRef name x

inferExpr :: Tagged Expr Scoped -> TC (Tagged Expr Typed, Typing)
inferExpr expr = do
    (expr', typing@(m, τ)) <- inferExpr_ expr
    return (T (tag expr, τ) expr', typing)

freshTy :: TC (Tagged Ty Typed)
freshTy = T (Nothing, KStar) . TyVar <$> fresh

unify :: [MonoEnv] -> [Tagged Ty Typed] -> TC a
unify = undefined

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
                    return (monoVar x α, α)
                Just typing -> instantiateTyping typing
        return (EVar (ref x), typing)
    ECon c -> do
        τ <- instantiateTy =<< lookupCon c
        return (ECon (ref c), (mempty, τ))
    EApp f arg -> do
        (f', (m₁, τ₁)) <- inferExpr f
        (arg', (m₂, τ₂)) <- inferExpr arg
        α <- freshTy
        (θ, m, t) <- unify [m₁, m₂] [τ₁, tyArr loc τ₂ α]
        let TyApp (T _ (TyApp (T _ TyFun) _)) τ = t
        return (EApp (θ ▷ f') (θ ▷ arg'), (m, τ))
    ELam pat body -> do
        (pat', (mPat, τPat)) <- inferPat pat
        (body', (mBody, τBody)) <- inferExpr body
        (θ, m, τ) <- unify [mPat, mBody] [tyArr loc τPat τBody]
        let m' = removeMonoVars (monoVars mPat) m
        return (ELam (θ ▷ pat') (θ ▷ body'), (m', τ))

inferPat :: Tagged Pat Scoped -> TC (Tagged Pat Typed, Typing)
inferPat (T loc pat) = case pat of
    PVar x -> do
        α <- freshTy
        return (T (loc, α) $ PVar (ref x), (monoVar x α, α))
    PCon con pats -> undefined
    PWildcard -> do
        α <- freshTy
        return (T (loc, α) PWildcard, (mempty, α))
