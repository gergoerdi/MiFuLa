{-# LANGUAGE DataKinds, GADTs #-}
import Mifula.Syntax
import Mifula.Syntax.Pretty ()
import Mifula.Parse (program)
import Mifula.Scope (scopeDefs, scopeTyDefT)
import Mifula.Scope.SC (runSC)
import Mifula.Kinding (runKC, kindDefs)
import Mifula.Typing (inferDefs)
import Mifula.Typing.TC (runTC)

import qualified Text.ParserCombinators.Parsec.IndentParser as IP

import Text.PrettyPrint.Leijen (pretty, vsep)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad (forM_)
import Data.Monoid
import Data.Either (partitionEithers)

decls :: [Decl]
decls = parseD prog
  where
    prog = unlines [ "data List a = Nil | Cons a (List a)"
                   , ""
                   , "id x = x"
                   , "id' = id (λ x → x)"
                   , "const x _ = x"
                   , "map f (Cons x xs) = Cons (f x) (mup f xs)"
                   , "map f Nil = Nil"
                   , "mapConst = map const"
                   , "mup f (Cons x xs) = Cons (f x) (map f xs)"
                   , "mup f Nil = Nil"
                   ]

    parseD s = case IP.parse program "" s of
        Right x -> x
        Left err -> error (show err)

main = do
    print $ vsep $ map pretty decls
    putStrLn "--==================--"

    let (tydefs, defs) = partitionEithers $ map toEither decls
        toEither (DeclTyDef tydef) = Left tydef
        toEither (DeclDef def) = Right def
        defsP = DefsUngrouped defs

    let scope = do
            tydefsS <- mapM scopeTyDefT tydefs
            defsS <- scopeDefs defsP
            return (tydefsS, defsS)
    let (tydefsS, defsS) = case runSC (map unTag tydefs) scope of
            Left err -> error $ show err
            Right x -> x
    print $ pretty defsS
    putStrLn "--==================--"

    let conMap :: Map (Con Kinded) (Tagged Ty Typed)
        conMap = runKC $ undefined tydefsS
        defsK = runKC $ kindDefs defsS

    let (defsT, env) = runTC conMap mempty (inferDefs defsK)
    print $ pretty env
