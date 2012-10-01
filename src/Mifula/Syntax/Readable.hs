{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Mifula.Syntax.Readable
       ( Readable
       , runReadable
       , readableTv
       , readableTy, readableTyT
       ) where

import Mifula.Syntax

import Control.Monad.Tardis
import Mifula.Fresh
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Control.Arrow (first, second)
import Control.Applicative
import Data.Maybe

newtype Readable a = Readable{ unReadable :: Tardis (Set String) (Stream String, Map Id (Ref Parsed)) a }
                   deriving (Functor, Applicative, Monad)

runReadable :: Readable a -> a
runReadable (Readable tardis) = result
  where
    (result, (tvNames, _)) = runTardis tardis (mempty, (niceNames, mempty))

    niceNames :: Stream String
    niceNames = Stream.filter unused $ prepend preferred failsafe
      where
        preferred = ["α", "β", "γ"] ++ map (:[]) ['a'..'z']
        failsafe = fmap (\i -> 't':show i) $ Stream.iterate succ 1
        unused = not . (`Set.member` tvNames)

remember :: Ref Typed -> Readable (Ref Parsed)
remember ref = do
    Readable $ modifyBackwards $ Set.insert name
    return $ NameRef name
  where
    name = refName ref

instance MonadFresh (Ref Parsed) Readable where
    fresh = Readable $ do
        ~(Cons s ss) <- getsPast fst
        modifyForwards . first $ const ss
        return $ NameRef s

prepend :: [a] -> Stream a -> Stream a
prepend (x:xs) ys = Cons x $ prepend xs ys
prepend [] ys = ys

readableTv :: Tv Typed -> Readable (Tv Parsed)
readableTv tv = TvNamed <$> case tv of
    TvNamed ref -> remember ref
    TvFresh id -> do
        lookup <- Readable . getsPast $ Map.lookup id . snd
        case lookup of
            Just name -> return name
            Nothing -> do
                name <- fresh
                Readable . modifyForwards . second $ Map.insert id name
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
