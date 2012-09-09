{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Fresh (MonadFresh(..), SupplyId, runSupplyId) where

import Mifula.Id

import Control.Monad.State
import Control.Applicative
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream

class (Monad m) => MonadFresh a m | m -> a where
    fresh :: m a

newtype SupplyId a = SupplyId{ unSupplyId :: State (Stream Id) a }
                   deriving (Functor, Applicative, Monad)

instance MonadFresh Id SupplyId where
    fresh = SupplyId $ do
        Cons x xs <- get
        put xs
        return x

runSupplyId :: SupplyId a -> a
runSupplyId m = evalState (unSupplyId m) $ Stream.iterate succ (toEnum 0)
