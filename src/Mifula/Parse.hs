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

type P a = IP.IndentCharParser () a

lexer = T.makeTokenParser $ L.haskellStyle {
    T.reservedNames = ["let", "in", "where", "data"],
    T.reservedOpNames = ["λ", "\\", "→", "->", "=", "_", "|"]
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

arr :: P ()
arr = reservedOp "->" <|> reservedOp "→"

lambda :: P ()
lambda = reservedOp "\\" <|> reservedOp "λ"

conname :: P (Con Parsed)
conname = do
    name@(n:_) <- identifier
    guard $ isUpper n
    return $ NameRef name

varname :: P (Var Parsed)
varname = do
    name@(n:_) <- identifier
    guard $ isLower n
    return $ NameRef name

tv :: P (Tv Parsed)
tv = TvNamed <$> varname

loc p = do
    pos <- getPos
    T pos <$> p

getPos :: P SourcePos
getPos = getPosition

ty :: Bool -> P (Tagged Ty Parsed)
ty needParens = buildExpressionParser table term <?> "type expression"
  where
    table = [ [Infix tyApp AssocLeft]
            , [Infix tyFun AssocRight]
            ]
    term = parens (ty False) <|> loc (try tyVar <|> tyCon)

    tyFun = do
        arr
        pos <- getPos
        return $ \t u -> T pos $ TyApp (T pos $ TyApp (T pos TyFun) t) u

    tyApp = do
        guard (not needParens)
        -- whiteSpace
        pos <- getPos
        return $ \t u -> T pos $ TyApp t u
    tyVar = TyVar <$> tv
    tyCon = TyCon <$> conname

pat :: Bool -> P (Tagged Pat Parsed)
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

locals :: P (Defs Parsed)
locals = do
    mlocals <- optionMaybe $ IP.block $ do
        reservedOp "where"
        IP.block $ defs
    return $ noLocals `fromMaybe` mlocals
  where
    noLocals = DefsUngrouped []

match :: Var Parsed -> P (Tagged Match Parsed)
match f = try $ loc $ do
    f' <- varname
    guard $ f' == f
    pats <- many1 $ pat True
    reservedOp "="
    body <- IP.lineFold expr
    locals <- locals
    return $ Match pats locals body

expr :: P (Tagged Expr Parsed)
expr = buildExpressionParser table term <?> "expression"
  where
    table = [[Infix eApp AssocLeft]]
    term = parens expr <|> loc (eLit <|> eLam <|> try eVar <|> eCon)

    eVar = EVar <$> varname
    eCon = ECon <$> conname
    eApp = do
        -- whiteSpace
        pos <- getPos -- TODO
        return $ \f x -> T pos $ EApp f x

    eLit = ELit <$> lit

    lit = LInt <$> integer

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
        return $ ELet (DefsUngrouped defs) body

defs :: P (Defs Parsed)
defs = DefsUngrouped <$> many1 def

def :: P (Tagged Def Parsed)
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

tydef :: P (Tagged TyDef Parsed)
tydef = loc tdData
  where
    tdData = do
        reserved "data"
        name <- conname
        formals <- many varname
        reservedOp "="
        cons <- IP.lineFold $ conDef `sepBy1` reservedOp "|"
        return $ TDData name formals cons

conDef :: P (Tagged ConDef Parsed)
conDef = loc $ do
    name <- conname
    tys <- many (ty True)
    return $ ConDef name tys

program :: P [Decl]
program = do
    prog <- program'
    eof
    return prog
  where
    program' = many $ (DeclTyDef <$> tydef) <|> (DeclDef <$> def)

