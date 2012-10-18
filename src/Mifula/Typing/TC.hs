{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
module Mifula.Typing.TC where

import Mifula.Fresh
import Mifula.Syntax
import Mifula.Prims
import Mifula.Typing.MonoEnv
import Mifula.Typing.PolyEnv
import Control.Applicative
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Reader

data R = R{ rCons :: Map (ConB (Kinded Out)) (Tagged Ty (Kinded Out))
          , rPolyEnv :: PolyEnv
          }
       deriving Show

newtype TC a = TC{ unTC :: ReaderT R SupplyId a }
             deriving (Functor, Applicative, Monad)

instance MonadFresh (Tv Typed) TC where
    fresh = TvFresh <$> (TC . lift $ fresh)

runTC :: Map (ConB (Kinded Out)) (Tagged Ty (Kinded Out))
      -> PolyEnv
      -> TC a -> a -- TODO: errors
runTC cons polyEnv tc = runSupplyId $ runReaderT (unTC tc) r
  where
    r = R{ rCons = cons
         , rPolyEnv = polyEnv
         }

internalError :: String -> TC a
internalError s = error $ unwords ["Internal error:", s]

-- noteError :: UnificationError (Tv Typed) (Tagged Ty Typed) -> TC ()
-- noteError = undefined

withEnv :: PolyEnv -> TC a -> TC a
withEnv env = TC . local addEnv . unTC
  where
    addEnv r@R{..} = r{ rPolyEnv = env <> rPolyEnv }

lookupVar :: Var (Kinded Out) -> TC (Maybe Typing)
lookupVar (BindingRef b) = TC . asks $ lookupPolyVar b . rPolyEnv
-- lookupVar (PrimRef _ p) = return $ Just $ primVarTy p :@ mempty

tunnelTy :: Tagged Ty (Kinded Out) -> Tagged Ty Typed
tunnelTy (T tag τ) = T tag $ go τ
  where
    go :: Ty (Kinded Out) -> Ty Typed
    go τ = case τ of
        TyCon con -> TyCon $ ref con
        TyVar (TvNamed (BindId name id)) -> TyVar . TvNamed $ BindId name id
        TyApp t u -> TyApp (tunnelTy t) (tunnelTy u)
        TyFun -> TyFun

    ref :: Ref ns (Kinded Out) -> Ref ns Typed
    ref (BindingRef (BindId name id)) = BindingRef $ BindId name id
    ref (PrimRef prim) = PrimRef prim

lookupCon :: ConB (Kinded Out) -> TC (Tagged Ty Typed)
lookupCon con = do
    mty <- TC . asks $ Map.lookup con . rCons
    maybe fail (return . tunnelTy) mty
  where
    fail = internalError $ unwords ["constructor not found:", show con]
