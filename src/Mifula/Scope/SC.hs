{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Mifula.Scope.SC
       ( SC, runSC
       , refVar, refCon, defPVar
       , listenVars, withVars, listenPVars
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

data R = R{ rVars :: Set Var
          , rCons :: Set Con
          }

data W = W{ wRefs :: Set Var
          , wPVars :: Set Var
          , wErrors :: [ScopeError]
          }

instance Monoid W where
    mempty = W mempty mempty mempty
    (W refs defs errors) `mappend` (W refs' defs' errors') = W (refs <> refs') (defs <> defs') (errors <> errors')

newtype SC a = SC{ unSC :: ReaderT R (Writer W) a }
             deriving (Functor, Applicative, Monad)

runSC :: Set Con -> SC a -> Either [ScopeError] a
runSC cons sc = case runWriter $ runReaderT (unSC sc) r₀ of
    (x, w) -> case wErrors w of
        [] -> Right x
        errs -> Left errs
  where
    r₀ = R{ rVars = mempty
          , rCons = cons
          }

listenVars :: Set Var -> SC a -> SC (a, Set Var)
listenVars newVars = listenRefs (`Set.member` newVars) . withVars newVars

withVars :: Set Var -> SC a -> SC a
withVars newVars = SC . local addVars . unSC
  where
    addVars :: R -> R
    addVars r@R{ rVars } = r{ rVars = rVars `Set.union` newVars }

listenRefs :: (Var -> Bool) -> SC a -> SC (a, Set Var)
listenRefs isLocal sc = do
    (x, w) <- SC . censor noRefs . listen . unSC $ sc
    let vars = wRefs w
        (varsHere, varsThere) = Set.partition isLocal vars
    SC . tell $ mempty{ wRefs = varsThere }
    return (x, varsHere)
  where
    noRefs :: W -> W
    noRefs w = w{ wRefs = mempty }

listenPVars :: SC a -> SC (a, Set Var)
listenPVars sc = do
    (x, w) <- SC . censor noPVars . listen . unSC $ sc
    return (x, wPVars w)
  where
    noPVars :: W -> W
    noPVars w = w{ wPVars = mempty }

scopeError :: ScopeError -> SC ()
scopeError err = SC . tell $ mempty{ wErrors = [err]} -- TODO: error locations

tellVar :: Var -> SC ()
tellVar x = SC . tell $ mempty{ wRefs = Set.singleton x }

tellPVar :: Var -> SC ()
tellPVar x = SC . tell $ mempty{ wPVars = Set.singleton x }

refVar :: Var -> SC Var
refVar x = do
    inScope <- SC $ asks $ Set.member x . rVars
    unless inScope $ do
        scopeError $ SEUnresolvedVar x
    tellVar x
    return x

refCon :: Con -> SC Var
refCon con = do
    knownCon <- SC $ asks $ Set.member con . rCons
    unless knownCon $ do
        scopeError $ SEUnresolvedCon con
    return con

defPVar :: Var -> SC Var
defPVar var = do
    tellPVar var
    return var
