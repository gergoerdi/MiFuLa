{-# LANGUAGE DataKinds #-}
import Mifula.Syntax
import Mifula.Parse (defs, parseWhole)

import qualified Text.ParserCombinators.Parsec.IndentParser as IP

import Text.PrettyPrint.Leijen

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Prelude hiding (mapM)
import Data.Default

foo = parseD prog
  where
    prog = unlines [ "id x = x"
                   , "id' = id (λ x → x)"
                   , "const x _ = x"
                   , "map f (Cons x xs) = Cons (f x) (mup f xs)"
                   , "map f Nil = Nil"
                   , "mup f (Cons x xs) = Cons (f x) (map f xs)"
                   , "mup f Nil = Nil"
                   , "mapConst = map const"
                   ]

    parseD s = case IP.parse (parseWhole defs) "" s of
        Right x -> x
        Left err -> error (show err)

main = print foo
