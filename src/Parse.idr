module Parse

import Text.Lexer
import Text.Parser

import Types
import AST as AST
import Parse.Lex as Lex
import Parse.Token as Tok

%default total
%access public export

ident : Grammar TypeToken True String
ident = do
  name <- match Tok.Ident
  the (Grammar _ False _) $ pure name

-- TODO dedupe string literals
primType : Grammar TypeToken True AST.TDef
primType = do
  tname <- match Tok.PrimType
  the (Grammar _ False _) $ case tname of
    "Void" => pure AST.Void
    "Unit" => pure AST.Unit
    _      => fail "unrecognised primitive type"

mutual
  nOp : NOpType -> (AST.TDef -> AST.TDef -> List (AST.TDef) -> AST.TDef) -> Grammar TypeToken True AST.TDef
  nOp op ctor = do
    match (Tok.Punct LParen)
    match (Tok.NOp op)
    x <- typedef
    y <- typedef
    zs <- assert_total $ manyTill (match $ Tok.Punct RParen) typedef
    pure (ctor x y zs)

  prod : Grammar TypeToken True AST.TDef
  prod = nOp ProdNO AST.Prod

  sum : Grammar TypeToken True AST.TDef
  sum = nOp SumNO AST.Sum

  mu : Grammar TypeToken True AST.TDef
  mu = do
    match (Tok.Punct LParen)
    match Tok.Mu
    name <- ident
    def <- typedef
    match (Tok.Punct RParen)
    pure $ AST.Mu name [def]

  var : Grammar TypeToken True AST.TDef
  var = do
    match (Tok.Punct LParen)
    match Tok.Var
    n <- match Tok.Number
    match (Tok.Punct RParen)
    pure (AST.Var n)

  typedef : Grammar TypeToken True AST.TDef
  typedef = primType
        <|> prod
        <|> sum
        <|> mu
        <|> var
