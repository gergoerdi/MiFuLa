{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Mifula.Scope.SC
       ( SC, unSC
       , refVar, refCon, refPVar
       , listenVars
       ) where

import Mifula.Syntax

import Control.Error
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Arrow (first, second)

data ScopeError = SEUnresolvedCon Con
                | SEUnresolvedVar Var
                | SEPatternConflict Var
                deriving Show

data R = R{ rVars :: Set Var }

newtype SC a = SC{ unSC :: ReaderT R (Writer (Set Var, [ScopeError])) a }
             deriving (Functor, Applicative, Monad)

listenVars :: Set Var -> SC a -> SC (a, Set Var)
listenVars newVars f = do
    (x, vars) <- SC . censor (first mempty) $
       fmap (second fst) . listen $
       local addVars . unSC $ f
    let (varsHere, varsThere) = Set.partition (`Set.member` newVars) vars
    SC . tell $ (varsThere, mempty)
    return (x, varsHere)
  where
    addVars :: R -> R
    addVars r@R{ rVars } = r{ rVars = rVars `Set.union` newVars }

refVar :: Var -> SC Var
refVar x = do
    inScope <- SC $ asks $ Set.member x . rVars
    -- TODO: error locations
    SC . tell $ if inScope
                then (Set.singleton x, mempty)
                else (mempty, [SEUnresolvedVar x])
    return x

refCon :: Con -> SC Var
refCon con = do
    -- TODO: check
    return con

refPVar :: Var -> SC Var
refPVar var = do
    -- TODO
    return var
