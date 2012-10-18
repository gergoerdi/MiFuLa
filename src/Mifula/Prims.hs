{-# LANGUAGE GADTs, DataKinds #-}
module Mifula.Prims where

import Mifula.Syntax

import Data.Map (Map)
import qualified Data.Map as Map

primVarRef :: Var Parsed -> Maybe (PrimId NSVar)
primVarRef = (Map.lookup `flip` prims) . refName
  where
    prims :: Map String (PrimId NSVar)
    prims = Map.fromList [("plus", PrimPlus)]

primTyConKind :: PrimId NSTyCon -> Kind Out
primTyConKind p = case p of
    PrimInt -> KStar

-- primTy :: String -> PrimId NSTyCon -> Tagged Ty (Kinded Out)
-- primTy name p = T (Nothing, κ) $ TyCon $ PrimRef name p
--   where
--     κ = primTyConKind p

primVarTy :: PrimId NSVar -> Tagged Ty Typed
primVarTy p = case p of
    PrimPlus -> int ~> int ~> int
  where
    tag :: Kind Out -> Ty Typed -> Tagged Ty Typed
    tag κ = T (Nothing, κ)

    infixr ~>
    t ~> u = tag KStar $ TyApp (tag (KStar `KArr` KStar) $ TyApp fun t) u
      where
        fun = tag (KStar `KArr` KStar `KArr` KStar) TyFun

    primTy :: String -> PrimId NSTyCon -> Tagged Ty Typed
    primTy name p = T (Nothing, κ) $ TyCon $ PrimRef name p
      where
        κ = primTyConKind p

    int = primTy "Int" PrimInt

