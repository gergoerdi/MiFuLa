{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Id (Id, idHash) where

newtype Id = Id{ idHash :: Int }
           deriving (Eq, Ord, Enum, Show)
