{-# LANGUAGE DataKinds #-}
module Mifula.Parse where

import Mifula.Syntax

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import qualified Text.ParserCombinators.Parsec.Language as L
import qualified Text.ParserCombinators.Parsec.IndentParser.Token as IT
import qualified Text.ParserCombinators.Parsec.IndentParser as IP

import Control.Monad
import Data.Char
-- import Data.Either
import Data.Maybe

import Control.Applicative ((<$>)) -- IndentParser uses Parsec 2, which doesn't expose an Applicative instance...

lexer = T.makeTokenParser $ L.haskellStyle {
    T.reservedNames = ["let", "in", "where"],
    T.reservedOpNames = ["λ", "\\", "→", "->", "=", "_"]
    }

brackets   = IT.brackets lexer
colon      = IT.colon lexer
comma      = IT.comma lexer
semi       = IT.semi lexer
parens     = IT.parens lexer
integer    = IT.integer lexer
natural    = IT.natural lexer
reserved   = IT.reserved lexer
reservedOp = IT.reservedOp lexer
identifier = IT.identifier lexer
whiteSpace = IT.whiteSpace lexer

arr = reservedOp "->" <|> reservedOp "→"
lambda = reservedOp "\\" <|> reservedOp "λ"

conname = do name@(n:_) <- identifier
             guard $ isUpper n
             return name

varname = do name@(n:_) <- identifier
             guard $ isLower n
             return name

loc p = do
    pos <- getPos
    T pos <$> p

getPos :: IP.IndentCharParser () SourcePos
getPos = getPosition

ty :: IP.IndentCharParser () (Tagged Ty Parsed)
ty = buildExpressionParser table term <?> "type expression"
  where
    table = [ [Infix tyApp AssocRight]
            , [Infix tyFun AssocRight]
            ]
    term = parens ty <|> loc (try tyVar <|> tyCon)

    tyFun = do
        arr
        pos <- getPos
        return $ \t u -> T pos $ TyApp (T pos $ TyApp (T pos TyFun) t) u

    tyApp = do
        -- whiteSpace
        pos <- getPos
        return $ \t u -> T pos $ TyApp t u
    tyVar = TyVar <$> varname
    tyCon = TyCon <$> conname

pat :: Bool -> IP.IndentCharParser () (Tagged Pat Parsed)
pat needParens = pCon' <|> try pWildcard <|> pVar <|> parens (pat False)
  where
    pVar = loc $ PVar <$> varname

    pCon' = if needParens then try pCon0 <|> parens pCon else pCon

    pCon = loc $ do
        con <- conname
        pats <- many (pat True)
        return $ PCon con pats

    pCon0 = loc $ do
        con <- conname
        return $ PCon con []

    pWildcard = loc $ do
        reservedOp "_"
        return $ PWildcard

locals :: IP.IndentCharParser () (Tagged Defs Parsed)
locals = do
    mlocals <- optionMaybe $ IP.block $ do
        reservedOp "where"
        IP.block $ defs
    return $ noLocals `fromMaybe` mlocals
  where
    noLocals = T () $ DefsUngrouped []

match :: Var -> IP.IndentCharParser () (Tagged Match Parsed)
match f = try $ loc $ do
    f' <- varname
    guard $ f' == f
    pats <- many1 $ pat True
    reservedOp "="
    body <- IP.lineFold expr
    locals <- locals
    return $ Match pats locals body

expr :: IP.IndentCharParser () (Tagged Expr Parsed)
expr = buildExpressionParser table term <?> "expression"
  where
    table = [[Infix eApp AssocLeft]]
    term = parens expr <|> loc (eLam <|> try eVar <|> eCon)

    eVar = EVar <$> varname
    eCon = ECon <$> conname
    eApp = do
        -- whiteSpace
        pos <- getPos -- TODO
        return $ \f x -> T pos $ EApp f x

    eLam = do
        lambda
        p <- pat True
        arr
        body <- expr
        return $ ELam p body

    eLet = do
        reserved "let"
        defs <- IP.block $ many1 def
        reserved "in"
        body <- expr
        return $ ELet (T () $ DefsUngrouped defs) body

defs :: IP.IndentCharParser () (Tagged Defs Parsed)
defs = T () . DefsUngrouped <$> many1 def

def :: IP.IndentCharParser () (Tagged Def Parsed)
def = loc $ try defVar <|> defFun
  where
    defVar = do
        var <- varname
        reservedOp "="
        e <- IP.lineFold expr
        locals <- locals
        return $ DefVar var locals e

    defFun = do
        fun <- lookAhead varname
        ms <- many1 $ match fun
        return $ DefFun fun ms

parseWhole p = do
    x <- p
    eof
    return x

{-
program = do (decls, defs) <- liftM partitionEithers $ many $ whiteSpace >> (decl <|> vardef)
             return $ Program decls defs

    where decl = Left <$> typedecl
          vardef = Right <$> def
-}
