{-# LANGUAGE DataKinds, GADTs #-}
module Mifula.Typing where

import Mifula.Typing.TC
import Mifula.Syntax
import Control.Applicative
import Mifula.Fresh
import Data.Monoid

instantiateTyping :: Typing -> TC Typing
instantiateTyping = undefined

instantiateTy :: Tagged Ty Typed -> TC (Tagged Ty Typed)
instantiateTy = undefined

ref :: Ref Scoped -> Ref Typed
ref (IdRef name x) = IdRef name x

inferExpr :: Expr Scoped -> TC (Expr Typed, Typing)
inferExpr expr = case expr of
    EVar x -> do
        typing <- do
            mtyping <- lookupPolyVar x
            case mtyping of
                Nothing -> do
                    α <- T (Nothing, KStar) . TyVar <$> fresh
                    return (monoVar x α, α)
                Just typing -> instantiateTyping typing
        return (EVar (ref x), typing)
    ECon c -> do
        τ <- instantiateTy =<< lookupCon c
        return (ECon (ref c), (mempty, τ))
