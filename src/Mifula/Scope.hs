{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Mifula.Scope (scopeDefs) where

import Mifula.Syntax
import Mifula.Scope.SC

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Monad (forM)

import qualified Data.Graph as G
import Data.Set (Set)
import qualified Data.Set as Set

scopeDefs :: Defs Parsed -> SC (Defs Scoped)
scopeDefs (DefsUngrouped defs) = do
    edges <- forM defsWithNames $ \(name, def) -> do
        (def', refs) <- listenVars newVars $ liftTag scopeDef def
        return (def', name, Set.toList refs)
    return $ DefsGrouped $ topsort $ edges
  where
    defsWithNames :: [(Var, Tagged Def Parsed)]
    defsWithNames = map (defName . unTag &&& id) defs

    newVars :: Set Var
    newVars = Set.fromList $ map fst defsWithNames

    topsort = map G.flattenSCC . G.stronglyConnComp

scopeDef :: Def Parsed -> SC (Def Scoped)
scopeDef def = case def of
    DefVar var locals body ->
        withLocals locals $ \locals' -> do
            DefVar var locals' <$> scopeExprT body
    DefFun fun matches ->
        DefFun fun <$> mapM (liftTag scopeMatch) matches

scopeMatch :: Match Parsed -> SC (Match Scoped)
scopeMatch (Match pats locals body) = do
    withPats pats $ \pats' -> do
        withLocals locals $ \locals' -> do
            Match pats' locals' <$> scopeExprT body

scopeExpr :: Expr Parsed -> SC (Expr Scoped)
scopeExpr expr = case expr of
    EVar x -> EVar <$> refVar x
    ECon con -> ECon <$> refCon con
    EApp f x -> EApp <$> scopeExprT f <*> scopeExprT x
    ELam pat body ->
        withPat pat $ \pat' -> do
            ELam pat' <$> scopeExprT body
    ELet defs body ->
        ELet <$> liftTag scopeDefs defs <*> scopeExprT body -- TODO

scopeExprT = liftTag scopeExpr

withPat :: Tagged Pat Parsed -> (Tagged Pat Scoped -> SC a) -> SC a
withPat pat f = undefined

withPats :: [Tagged Pat Parsed] -> ([Tagged Pat Scoped] -> SC a) -> SC a
withPats pats f = undefined

withLocals :: Tagged Defs Parsed -> (Tagged Defs Scoped -> SC a) -> SC a
withLocals defs f = undefined

scopePat :: Pat Parsed -> SC (Pat Scoped)
scopePat pat = case pat of
    PVar var -> PVar <$> refPVar var
    PCon con pats -> PCon <$> refCon con <*> mapM (liftTag scopePat) pats
    PWildcard -> return PWildcard

liftTag :: (AST a, Tag a Parsed ~ Tag a Scoped)
        => (a Parsed -> SC (a Scoped))
        -> Tagged a Parsed
        -> SC (Tagged a Scoped)
liftTag f tx = T (tag tx) <$> f (unTag tx)
