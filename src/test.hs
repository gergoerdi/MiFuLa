{-# LANGUAGE DataKinds #-}
import Mifula.Syntax
import Mifula.Syntax.Pretty ()
import Mifula.Parse (defs, parseWhole)
import Mifula.Scope (scopeDefs)
import Mifula.Scope.SC (runSC)
import Mifula.Typing (inferDefs)
import Mifula.Typing.TC (runTC)

import qualified Text.ParserCombinators.Parsec.IndentParser as IP

import Text.PrettyPrint.Leijen

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad (forM_)
import Data.Monoid

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
    let (conIDs, foo') = case runSC conNames $ fmap fst $ scopeDefs foo of
            Left err -> error $ show err
            Right x -> x
    print $ pretty foo'
    putStrLn "--==================--"
    print conIDs
    let conMap :: Map (Con Scoped) (Tagged Ty Typed)
        conMap = Map.fromList . map f . Set.toList $ conIDs
          where
            f con = (con, cons ! refName con)
    forM_ (Map.toList conMap) $ \(con, ty) -> do
        print con
        print $ pretty ty
    let foo'' = runTC conMap mempty (inferDefs foo')
    print foo''
    -- return foo'
  -- where
  --   cons :: Map (Con Scoped) (Tagged Ty Typed)
    -- cons = Map.fromList [
  where
    tyList :: Tagged Ty Typed -> Tagged Ty Typed
    tyList = T (Nothing, KStar) . TyApp (T (Nothing, KStar `KArr` KStar) tyCon)
      where
        tyCon = TyCon $ IdRef "List" (toEnum 200)

    a :: Tagged Ty Typed
    a = T (Nothing, KStar) $ TyVar $ TvNamed $ IdRef "a" (toEnum 100)

    cons :: Map String (Tagged Ty Typed)
    cons = Map.fromList [ ("Nil", tyList a)
                        , ("Cons", a ~> tyList a ~> tyList a)
                        ]
      where
        infixr ~>
        t ~> u = T (Nothing, KStar) $ TyApp (T (Nothing, KStar `KArr` KStar) $ TyApp tyFun t) u
        tyFun = T (Nothing, KStar `KArr` KStar `KArr` KStar) TyFun

    conNames :: Set (Con Parsed)
    conNames = Set.mapMonotonic NameRef . Map.keysSet $ cons
