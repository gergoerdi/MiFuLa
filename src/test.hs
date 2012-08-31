{-# LANGUAGE DataKinds #-}
import Mifula.Syntax
import Mifula.Parse (defs, parseWhole)
import Mifula.Scope (scopeDefsT)
import Mifula.Scope.SC (runSC)

import qualified Text.ParserCombinators.Parsec.IndentParser as IP

import Text.PrettyPrint.Leijen

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Prelude hiding (mapM)
import Data.Default

foo :: Tagged Defs Parsed
foo = parseD prog
  where
    prog = unlines [ "id x = x"
                   , "id' = id (λ x → x)"
                   , "const x _ = x"
                   , "map f (Cons x xs) = Cons (f x) (mup f xs)"
                   , "map f Nil = Nil"
                   , "mapConst = map const"
                   , "mup f (Cons x xs) = Cons (f x) (map f xs)"
                   , "mup f Nil = Nil"
                   ]

    parseD s = case IP.parse (parseWhole defs) "" s of
        Right x -> x
        Left err -> error (show err)

main = do
    print $ pretty foo
    putStrLn "--==================--"
    let foo' = case runSC (Set.fromList ["Cons", "Nil"]) $ scopeDefsT foo of
            Left err -> error $ show err
            Right (foo', _) -> foo'
    print $ pretty foo'
