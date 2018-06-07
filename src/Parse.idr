module Parse

import Text.Lexer
import Text.Parser
import Lex as Lex
import Types
import Token as Tok
import AST as AST

%default total
%access public
export

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
  binOp : BinOpType -> (AST.TDef -> AST.TDef -> AST.TDef) -> Grammar TypeToken True AST.TDef
  binOp op ctor = do
    match (Tok.Punct LParen)
    match (Tok.BinOp op)
    x <- typedef
    y <- typedef
    match (Tok.Punct RParen)
    pure (ctor x y)

  prod : Grammar TypeToken True AST.TDef
  prod = binOp ProdBO AST.Prod

  sum : Grammar TypeToken True AST.TDef
  sum = binOp SumBO AST.Sum

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
