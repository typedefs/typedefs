module Token

import Text.Lexer

%access public
export

data BinOpType = SumBO | ProdBO

Eq BinOpType where
  (==) SumBO  SumBO  = True
  (==) ProdBO ProdBO = True
  (==) _      _      = False

data TypeKind
  = Ident
  | PrimType
  | Var
  | Mu
  | BinOp BinOpType
  | Punct
  | Whitespace

TokenKind TypeKind where
  TokType Ident            = String
  TokType PrimType         = String
  TokType Var              = Int
  TokType Mu               = Unit
  TokType (BinOp o)        = String
  TokType Punct            = ()
  TokType Whitespace       = ()

  tokValue Ident       str = str
  tokValue PrimType    str = str
  tokValue Var         str = cast str
  tokValue Mu          str = ()
  tokValue (BinOp o)   str = str
  tokValue Punct       str = ()
  tokValue Whitespace  str = ()

Eq TypeKind where
  (==) Ident      Ident      = True
  (==) PrimType   PrimType   = True
  (==) Var        Var        = True
  (==) Mu         Mu         = True
  (==) (BinOp o1) (BinOp o2) = o1 == o2
  (==) Punct      Punct      = True
  (==) Whitespace Whitespace = True
  (==) _          _          = False

Show TypeKind where
  show Ident      = "Ident"
  show PrimType   = "PrimType"
  show Var        = "Var"
  show Mu         = "Mu"
  show BinOp      = "BinOp"
  show Punct      = "Punct"
  show Whitespace = "Whitespace"

TypeToken : Type
TypeToken = Token TypeKind
