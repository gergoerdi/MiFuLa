{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Mifula.Typing.Constraint
       ( MonadConstraint(..)
       , Cls
       , Constraint(..)
       , Constraints, allConstraints
       ) where

import Mifula.Syntax
import Mifula.Unify.UVar
import Control.Monad (liftM)
import Data.Monoid

type Cls = TyCon
data Constraint = ClassC (Cls Typed) (Tagged Ty Typed)
                deriving (Show)

class (Monad m) => MonadConstraint m where

instance (MonadConstraint m) => SubstUVars m Constraint (Tv Typed) where
    θ ▷ c = case c of
        ClassC cls τ -> liftM (ClassC cls) (θ ▷ τ)

newtype Constraints = Constraints{ allConstraints :: [Constraint] }
                    deriving (Monoid, Show)

instance (MonadConstraint m) => SubstUVars m Constraints (Tv Typed) where
    θ ▷ cs = liftM Constraints . mapM (θ ▷) . allConstraints $ cs
