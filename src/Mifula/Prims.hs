{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}
module Mifula.Prims (Prim, resolvePrim, desolvePrim) where

import Mifula.Syntax

import Data.Bimap (Bimap, (!>))
import qualified Data.Bimap as Bimap

class Prim (ns :: Namespace) where
    nameBimap :: Bimap String (PrimId ns)

resolvePrim :: (Prim ns) => Binding ns Parsed -> Maybe (Ref ns Scoped)
resolvePrim (BindName s) = fmap PrimRef $ Bimap.lookup s nameBimap

desolvePrim :: (Prim ns) => PrimId ns -> String
desolvePrim = (nameBimap !>)

instance Prim NSVar where
    nameBimap = Bimap.fromList [("plus", PrimPlus)]

instance Prim NSCon where
    nameBimap = Bimap.fromList []

instance Prim NSTyCon where
    nameBimap = Bimap.fromList [("Int", PrimInt)]

{-
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

-}
