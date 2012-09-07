{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Mifula.Fresh where

class (Monad m) => MonadFresh a m | m -> a where
    fresh :: m a
