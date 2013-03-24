{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Mifula.Typing.Constraint
       ( MonadConstraint(..)
       , Constraint(..)
       , Constraints(Constraints), allConstraints
       ) where

import Mifula.Syntax
import Mifula.Unify.UVar
import Control.Monad (liftM, (<=<))
import Data.Monoid
import Data.Foldable (foldMap)

type family ConstraintSubject (dir :: InOut) :: *
type instance ConstraintSubject In = Tagged Ty Typed
type instance ConstraintSubject Out = (Kind Out, Tv Typed)

data Constraint (dir :: InOut) = ClassC (Class Typed) (ConstraintSubject dir)
deriving instance (Show (Constraint In))
deriving instance (Show (Constraint Out))

class (Monad m) => MonadConstraint m where
    resolveConstraint :: Constraint In -> m (Constraints Out)

instance HasUVars (Constraint In) (Tv Typed) where
    uvars c = case c of
        ClassC cls τ -> uvars τ

instance HasUVars (Constraint Out) (Tv Typed) where
    uvars c = case c of
        ClassC cls (_, α) -> uvars α

newtype Constraints dir = Constraints{ allConstraints :: [Constraint dir] }
                        deriving (Monoid)
deriving instance (Show (Constraints In))
deriving instance (Show (Constraints Out))

instance (MonadConstraint m) => SubstUVars m (Constraints Out) (Tv Typed) where
    θ ▷ cs = liftM mconcat $ mapM (resolveConstraint <=< substitute) $ allConstraints cs
      where
        substitute :: (MonadConstraint m) => Constraint Out -> m (Constraint In)
        substitute c = case c of
            ClassC cls (κ, α) -> liftM (ClassC cls) $ do
                let τ = T (Nothing, κ) $ TyVar α
                τ' <- θ ▷ τ
                return $ τ'

instance HasUVars (Constraints Out) (Tv Typed) where
    uvars = foldMap uvars . allConstraints

