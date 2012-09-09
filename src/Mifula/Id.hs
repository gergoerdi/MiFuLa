{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Id (Id, idHash) where

import Data.Stream (Stream)
import qualified Data.Stream as Stream

newtype Id = Id{ idHash :: Int }
           deriving (Eq, Ord, Enum, Show)
