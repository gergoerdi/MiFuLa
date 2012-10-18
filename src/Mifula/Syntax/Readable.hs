{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
module Mifula.Syntax.Readable
       ( Readable
       , runReadable
       , readableTv
       , readableTy, readableTyT
       ) where

import Mifula.Syntax

import Mifula.Fresh
import Control.Monad.State
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Control.Applicative
import Data.Maybe

data S = S{ sUsed :: Set String
          , sFresh :: Stream String
          , sMapping :: Map Id (Ref Parsed)
          }

newtype Readable a = Readable{ unReadable :: State S a }
                   deriving (Functor, Applicative, Monad)

runReadable :: Readable a -> a
runReadable (Readable m) = result
  where
    (result, ~S{ sUsed = tvNames }) = runState m $ S mempty niceNames mempty

    niceNames :: Stream String
    niceNames = Stream.filter unused $ prepend preferred failsafe
      where
        preferred = ["α", "β", "γ"] ++ map (:[]) ['a'..'z']
        failsafe = fmap (\i -> 't':show i) $ Stream.iterate succ 1
        unused = not . (`Set.member` tvNames)

remember :: Ref Typed -> Readable (Ref Parsed)
remember ref = do
    Readable $ modify $ \s@S{..} -> s{ sUsed = Set.insert name sUsed }
    return $ NameRef name
  where
    name = refName ref

instance MonadFresh (Ref Parsed) Readable where
    fresh = Readable $ do
        ~(Cons n ns) <- gets sFresh
        modify $ \s -> s{ sFresh = ns }
        return $ NameRef n

prepend :: [a] -> Stream a -> Stream a
prepend (x:xs) ys = Cons x $ prepend xs ys
prepend [] ys = ys

readableTv :: Tv Typed -> Readable (Tv Parsed)
readableTv tv = TvNamed <$> case tv of
    TvNamed ref -> remember ref
    TvFresh id -> do
        lookup <- Readable . gets $ Map.lookup id . sMapping
        case lookup of
            Just name -> return name
            Nothing -> do
                name <- fresh
                Readable . modify $ \s@S{..} -> s{ sMapping = Map.insert id name sMapping }
                return name

readableTy :: Ty Typed -> Readable (Ty Parsed)
readableTy τ = case τ of
    TyCon con -> return $ TyCon $ NameRef . refName $ con
    TyVar tv -> TyVar <$> readableTv tv
    TyApp t u -> TyApp <$> readableTyT t <*> readableTyT u
    TyFun -> return TyFun

readableTyT :: Tagged Ty Typed -> Readable (Tagged Ty Parsed)
readableTyT (T (mloc, _) τ) = T loc <$> readableTy τ
  where
    loc = noPos `fromMaybe` mloc
