{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
module Mifula.Typing.TC where

import Mifula.Fresh
import Mifula.Syntax
import Mifula.Typing.MonoEnv
import Mifula.Typing.PolyEnv
import Control.Applicative
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Reader

data R = R{ rCons :: Map (Con Kinded) (Tagged Ty Typed)
          , rPolyEnv :: PolyEnv
          }
       deriving Show

newtype TC a = TC{ unTC :: ReaderT R SupplyId a }
             deriving (Functor, Applicative, Monad)

instance MonadFresh (Tv Typed) TC where
    fresh = TvFresh <$> (TC . lift $ fresh)

runTC :: Map (Con Kinded) (Tagged Ty Typed)
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

lookupVar :: Var Kinded -> TC (Maybe Typing)
lookupVar var = TC . asks $ lookupPolyVar var . rPolyEnv

lookupCon :: Con Kinded -> TC (Tagged Ty Typed)
lookupCon con =
    (TC . asks $ Map.lookup con . rCons) >>=
    maybe (internalError $ unwords ["constructor not found:", show con]) return
