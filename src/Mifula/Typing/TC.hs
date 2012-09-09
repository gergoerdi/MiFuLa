{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.TC where

import Mifula.Fresh
import Mifula.Syntax
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid

newtype TC a = TC{ unTC :: SupplyId a }
             deriving (Functor, Applicative, Monad)

newtype MonoEnv = MonoEnv{ monoVarMap :: Map (Var Scoped) (Tagged Ty Typed) }
                deriving Monoid

monoVar :: Var Scoped -> Tagged Ty Typed -> MonoEnv
monoVar = undefined

instance MonadFresh (Tv Typed) TC where
    fresh = TvFresh <$> TC fresh

type Typing = (MonoEnv, Tagged Ty Typed)

lookupPolyVar :: Var Scoped -> TC (Maybe Typing)
lookupPolyVar = undefined

lookupCon :: Con Scoped -> TC (Tagged Ty Typed)
lookupCon = undefined
