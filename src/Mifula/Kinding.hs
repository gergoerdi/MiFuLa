{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
module Mifula.Kinding where

import Mifula.Syntax

import Control.Applicative
import Mifula.Kinding.KC
import Mifula.Fresh
import Mifula.Unify.UVar
import Mifula.Unify.UEq
import Control.Monad (forM, (<=<))
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow (second)
import Data.Monoid

liftTag :: (AST a, Tag a Scoped ~ Tag a (Kinded dir))
        => (a Scoped -> KC (a (Kinded dir)))
        -> Tagged a Scoped
        -> KC (Tagged a (Kinded dir))
liftTag f tx = T pos <$> f (unTag tx)
  where
    pos = tag tx

kindTyDefs :: [Tagged TyDef Scoped] -> KC ([Tagged TyDef (Kinded Out)], Map (ConB (Kinded Out)) (Tagged Ty (Kinded Out)))
kindTyDefs tds = do
    tycons <- forM tds $ \td -> do
        let name = tdName $ unTag td
        α <- KVar <$> fresh
        return (name, td, α)

    let mapping :: Map (TyConB Scoped) (Kind In)
        mapping = Map.fromList $ map (\(name, _, α) -> (name, α)) tycons

    (tds', θ) <- unified $ withTyCons mapping $ do
        forM tycons $ \(_, td, α) -> do
            td' <- kindTyDef td
            assert $ kindOf td' :~: α
            return td'
    tds'' <- mapM (resolveKVars <=< (θ ▷)) tds'

    let cons :: Map (ConB (Kinded Out)) (Tagged Ty (Kinded Out))
        cons = Map.fromList $ concatMap (consOf . unTag) tds''

    return (tds'', cons)
  where
    tdName td = case td of
        TDAlias con _ _ -> con
        TDData con _ _ -> con

    consOf :: TyDef (Kinded Out) -> [(ConB (Kinded Out), Tagged Ty (Kinded Out))]
    consOf td = case td of
        TDAlias{} -> []
        TDData _ _ cons -> map (\(T (_, τ) (ConDef name _)) -> (name, τ)) cons

resolveKVars :: Tagged TyDef (Kinded In) -> KC (Tagged TyDef (Kinded Out))
resolveKVars (T (loc, κ) td) = T (loc, fixupKind κ) <$> case td of
    TDAlias name tvs τ -> TDAlias <$> kindBind name <*> mapM kindBind tvs <*> resolveTy τ
    TDData name tvs cons -> TDData <$> kindBind name <*> mapM kindBind tvs <*> mapM resolveCon cons
  where
    resolveTy :: Tagged Ty (Kinded In) -> KC (Tagged Ty (Kinded Out))
    resolveTy (T (loc, κ) τ) = T (loc, fixupKind κ) <$> case τ of
        TyCon name -> TyCon <$> kindRef name
        TyVar (TvNamed α) -> TyVar . TvNamed <$> kindBind α
        TyApp t u -> TyApp <$> resolveTy t <*> resolveTy u
        TyFun -> return TyFun

    resolveCon :: Tagged ConDef (Kinded In) -> KC (Tagged ConDef (Kinded Out))
    resolveCon (T (loc, τ) (ConDef name τs)) = do
        τ' <- resolveTy τ
        T (loc, τ') <$> (ConDef <$> kindBind name <*> mapM resolveTy τs)

fixupKind :: Kind In -> Kind Out
fixupKind κ = case κ of
    κ₁ `KArr` κ₂ -> fixupKind κ₁ `KArr` fixupKind κ₂
    _ -> KStar

kindTyDef :: Tagged TyDef Scoped -> KC (Tagged TyDef (Kinded In))
kindTyDef (T loc td) = case td of
    TDAlias con tvs τ -> do
        error "TODO"
    TDData name tvs cons -> do
        name' <- kindBind name
        params <- forM tvs $ \tv -> do
            α <- KVar <$> fresh
            tv' <- kindBind tv
            return (tv', T (Just loc, α) $ TyVar . TvNamed $ tv')
        let (tvs', τs) = unzip params

        let κs = map kindOf τs
            κ = foldr KArr KStar κs
            τ₀ = conTy (T (Just loc, κ) $ TyCon . BindingRef $ name') τs
        let mapping = Map.fromList $ zipWith (\tv τ -> (bindID tv, kindOf τ)) tvs τs
        withTyVars mapping $
          T (loc, κ) <$> TDData name' tvs' <$> mapM (kindCon τ₀) cons
  where
    conTy :: Tagged Ty (Kinded In) -> [Tagged Ty (Kinded In)] -> Tagged Ty (Kinded In)
    conTy = foldl (\t u -> let (κ `KArr` κ') = kindOf t in T (Just loc, κ') $ t `TyApp` u)

kindCon :: Tagged Ty (Kinded In) -> Tagged ConDef Scoped -> KC (Tagged ConDef (Kinded In))
kindCon τ₀ (T loc (ConDef con formals)) = do
    formals' <- forM formals $ \τ -> do
        τ'@(T (_, κ) _) <- kindTy τ
        assert $ κ :~: KStar
        return τ'
    con' <- kindBind con
    let τ = foldr (~>) τ₀ formals'
    return (T (loc, τ) $ ConDef con' formals')
  where
    (~>) :: Tagged Ty (Kinded In) -> Tagged Ty (Kinded In) -> Tagged Ty (Kinded In)
    t ~> u = tag KStar $ TyApp (tag (KStar `KArr` KStar) $ fun `TyApp` t) u

    tag :: Kind In -> Ty (Kinded In) -> Tagged Ty (Kinded In)
    tag κ = T (Just loc, κ)

    fun = tag (KStar `KArr` KStar `KArr` KStar) TyFun

kindTy :: Tagged Ty Scoped -> KC (Tagged Ty (Kinded In))
kindTy (T loc τ) = do
    (τ', κ) <- kindTy_ τ
    return $ T (Just loc, κ) τ'

kindOf :: (Tag a π ~ (b, Kind In)) => Tagged a π -> Kind In
kindOf (T (_, κ) _) = κ

kindTy_ :: Ty Scoped -> KC (Ty (Kinded In), Kind In)
kindTy_ τ = case τ of
    TyFun -> return (TyFun, KStar)
    t `TyApp` u -> do
        κ₀ <- KVar <$> fresh
        t' <- kindTy t
        u' <- kindTy u
        assert $ kindOf t' :~: (kindOf u' `KArr` κ₀)
        return (t' `TyApp` u', κ₀)
    TyVar α -> (,) <$> (TyVar <$> kindTv α) <*> lookupTyVar α
    TyCon con -> (,) <$> (TyCon <$> kindRef con) <*> lookupTyCon con

kindTv :: Tv Scoped -> KC (Tv (Kinded In))
kindTv (TvNamed x) = TvNamed <$> kindBind x

kindDefs :: Defs Scoped -> KC (Defs (Kinded Out))
kindDefs (DefsGrouped defss) = DefsGrouped <$> mapM (mapM $ liftTag kindDef) defss

kindDef :: Def Scoped -> KC (Def (Kinded Out))
kindDef def = case def of
    DefVar var locals body ->
        DefVar <$> kindBind var <*> kindDefs locals <*> liftTag kindExpr body
    DefFun fun matches ->
        DefFun <$> kindBind fun <*> mapM (liftTag kindMatch) matches

kindMatch :: Match Scoped -> KC (Match (Kinded Out))
kindMatch (Match pats locals body) = Match <$> mapM (liftTag kindPat) pats <*> kindDefs locals <*> liftTag kindExpr body

kindExpr :: Expr Scoped -> KC (Expr (Kinded Out))
kindExpr expr = case expr of
    EVar x -> EVar <$> kindRef x
    ECon con -> ECon <$> kindRef con
    ELit lit -> return $ ELit lit
    ELam pat body -> ELam <$> liftTag kindPat pat <*> liftTag kindExpr body
    EApp ef ex -> EApp <$> liftTag kindExpr ef <*> liftTag kindExpr ex
    ELet defs body -> ELet <$> kindDefs defs <*> liftTag kindExpr body

kindPat :: Pat Scoped -> KC (Pat (Kinded Out))
kindPat pat = case pat of
    PVar x -> PVar <$> kindBind x
    PCon con pats -> PCon <$> kindRef con <*> mapM (liftTag kindPat) pats
    PWildcard -> return PWildcard

kindBind :: (ScopedPass π ~ ScopedPass π') => Binding ns π -> KC (Binding ns π')
kindBind (BindId s x) = return $ BindId s x

kindRef :: (ScopedPass π ~ ScopedPass π') => Ref ns π -> KC (Ref ns π')
kindRef (BindingRef b) = BindingRef <$> kindBind b
kindRef (PrimRef p) = return $ PrimRef p
