module Lex

import Text.Lexer
import Token as Tok

%access public
export

isTDWhitespace : TypeToken -> Bool
isTDWhitespace tok = kind tok == Tok.Whitespace

ident : Lexer
ident = lower <+> alphaNums

-- TODO dedupe string literals
primType : Lexer
primType = exact "Unit" <|> exact "Void"

mu : Lexer
mu = exact "mu"

prod : Lexer
prod = exact "*"

sum : Lexer
sum = exact "+"

lparen : Lexer
lparen = exact "("

rparen : Lexer
rparen = exact ")"

typedefsTokenMap : TokenMap (Token TypeKind)
typedefsTokenMap = toTokenMap
  [ (spaces   , Tok.Whitespace)
  , (mu       , Tok.Mu)
  , (primType , Tok.PrimType)
  , (ident    , Tok.Ident)
  , (sum      , Tok.BinOp SumBO)
  , (prod     , Tok.BinOp ProdBO)
  , (lparen   , Tok.Punct LParen)
  , (rparen   , Tok.Punct RParen)
  ]

typedef : String -> Maybe (List TypeToken)
typedef str =
  case lex typedefsTokenMap str of
       (tokens, _, _, "") => Just $ map TokenData.tok tokens
       _                  => Nothing
