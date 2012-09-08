{-# LANGUAGE DataKinds #-}
import Mifula.Syntax
import Mifula.Syntax.Pretty ()
import Mifula.Parse (defs, parseWhole)
import Mifula.Scope (scopeDefs)
import Mifula.Scope.SC (runSC)

import qualified Text.ParserCombinators.Parsec.IndentParser as IP

import Text.PrettyPrint.Leijen

import Data.Set (Set)
import qualified Data.Set as Set

import Prelude hiding (mapM)

foo :: Defs Parsed
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
    let foo' = case runSC (Set.fromList [NameRef "Cons", NameRef "Nil"]) $ scopeDefs foo of
            Left err -> error $ show err
            Right (foo', _) -> foo'
    print $ pretty foo'
    -- return foo'
