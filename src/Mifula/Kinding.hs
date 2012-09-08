{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Kinding where

import Mifula.Syntax

import Control.Applicative
import Control.Monad.Identity

-- We don't have type signatures anywhere in Mifula, so this is a
-- no-op.
-- When either type signatures or datatype definitions are added, this
-- will need to become substantial.

newtype KC a = KC{ runKC :: Identity a }
             deriving (Functor, Applicative, Monad)

liftTag :: (AST a, Tag a Scoped ~ Tag a Kinded)
        => (a Scoped -> KC (a Kinded))
        -> Tagged a Scoped
        -> KC (Tagged a Kinded)
liftTag f tx = T pos <$> f (unTag tx)
  where
    pos = tag tx

kindDefs :: Defs Scoped -> KC (Defs Kinded)
kindDefs (DefsGrouped defss) = DefsGrouped <$> mapM (mapM $ liftTag kindDef) defss

kindDef :: Def Scoped -> KC (Def Kinded)
kindDef def = case def of
    DefVar var locals body ->
        DefVar <$> kindRef var <*> kindDefs locals <*> liftTag kindExpr body
    DefFun fun matches ->
        DefFun <$> kindRef fun <*> mapM (liftTag kindMatch) matches

kindMatch :: Match Scoped -> KC (Match Kinded)
kindMatch (Match pats locals body) = Match <$> mapM (liftTag kindPat) pats <*> kindDefs locals <*> liftTag kindExpr body

kindRef :: Ref Scoped -> KC (Ref Kinded)
kindRef (IdRef s x) = return $ IdRef s x

kindExpr :: Expr Scoped -> KC (Expr Kinded)
kindExpr expr = case expr of
    EVar x -> EVar <$> kindRef x
    ECon con -> ECon <$> kindRef con
    ELam pat body -> ELam <$> liftTag kindPat pat <*> liftTag kindExpr body
    EApp ef ex -> EApp <$> liftTag kindExpr ef <*> liftTag kindExpr ex
    ELet defs body -> ELet <$> kindDefs defs <*> liftTag kindExpr body

kindPat :: Pat Scoped -> KC (Pat Kinded)
kindPat pat = case pat of
    PVar x -> PVar <$> kindRef x
    PCon con pats -> PCon <$> kindRef con <*> mapM (liftTag kindPat) pats
    PWildcard -> return PWildcard
