{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Mifula.Scope (scopeDefs) where

import Mifula.Syntax
import Mifula.Scope.SC

import Control.Applicative
import Control.Monad (forM)

import qualified Data.Graph as G
import Data.Set (Set)
import qualified Data.Set as Set

scopeDefs :: Defs Parsed -> SC (Defs Scoped, Set (Var Scoped))
scopeDefs (DefsUngrouped defs) = do
    -- TODO: check conflicting names
    defsWithNames <- forM defs $ \def -> do
        var <- freshVar $ defName . unTag $ def
        return (var, def)
    let newVars = Set.fromList $ map fst defsWithNames

    edges <- forM defsWithNames $ \(name, def) -> do
        (def', refs) <- listenVars newVars $ liftTag scopeDef def
        return (def', name, Set.toList refs)
    return (DefsGrouped $ topsort edges, newVars)
  where
    topsort = map G.flattenSCC . G.stronglyConnComp

scopeDef :: Def Parsed -> SC (Def Scoped)
scopeDef def = case def of
    DefVar var locals body ->
        withDefs locals $ \locals' -> do
            DefVar <$> defVar var <*> pure locals' <*> scopeExprT body
    DefFun fun matches ->
        DefFun <$> defVar fun <*> mapM (liftTag scopeMatch) matches

scopeMatch :: Match Parsed -> SC (Match Scoped)
scopeMatch (Match pats locals body) = do
    withPats pats $ \pats' -> do
        withDefs locals $ \locals' -> do
            Match pats' locals' <$> scopeExprT body

scopeExpr :: Expr Parsed -> SC (Expr Scoped)
scopeExpr expr = case expr of
    EVar x -> EVar <$> refVar x
    ECon con -> ECon <$> refCon con
    EApp f x -> EApp <$> scopeExprT f <*> scopeExprT x
    ELam pat body -> do
        withPat pat $ \pat' -> do
            ELam pat' <$> scopeExprT body
    ELet defs body -> do
        withDefs defs $ \defs' -> do
            ELet defs' <$> scopeExprT body

scopeExprT = liftTag scopeExpr

withPat :: Tagged Pat Parsed -> (Tagged Pat Scoped -> SC a) -> SC a
withPat pat f = do
    (pat', pvars) <- listenPVars (liftTag scopePat pat)
    withVars pvars $ f pat'

withPats :: [Tagged Pat Parsed] -> ([Tagged Pat Scoped] -> SC a) -> SC a
withPats pats f = do
    (pats', pvarss) <- unzip <$> mapM (listenPVars . liftTag scopePat) pats
    -- TODO: check conflicts
    withVars (Set.unions pvarss) $ f pats'


withDefs :: Defs Parsed -> (Defs Scoped -> SC a) -> SC a
withDefs defs f = do
    (defs', newVars) <- scopeDefs defs
    withVars newVars $ f defs'

scopePat :: Pat Parsed -> SC (Pat Scoped)
scopePat pat = case pat of
    PVar var -> PVar <$> defPVar var
    PCon con pats -> PCon <$> refCon con <*> mapM (liftTag scopePat) pats
    PWildcard -> return PWildcard

liftTag :: (AST a, Tag a Parsed ~ SourcePos, Tag a Scoped ~ SourcePos)
        => (a Parsed -> SC (a Scoped))
        -> Tagged a Parsed
        -> SC (Tagged a Scoped)
liftTag f tx = T pos <$> atPosition pos (f (unTag tx))
  where
    pos = tag tx
