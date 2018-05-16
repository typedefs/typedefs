module Token

import Text.Lexer

%access public
export

data BinOpType = SumBO | ProdBO

Eq BinOpType where
  (==) SumBO  SumBO  = True
  (==) ProdBO ProdBO = True
  (==) _      _      = False

data ParenType = LParen | RParen

Eq ParenType where
  (==) LParen LParen = True
  (==) RParen RParen = True
  (==) _      _      = False

data TypeKind
  = Ident
  | PrimType
  | Var
  | Mu
  | BinOp BinOpType
  | Punct ParenType
  | Whitespace

TokenKind TypeKind where
  TokType Ident            = String
  TokType PrimType         = String
  TokType Var              = Int
  TokType Mu               = Unit
  TokType (BinOp o)        = String
  TokType (Punct p)        = ()
  TokType Whitespace       = ()

  tokValue Ident       str = str
  tokValue PrimType    str = str
  tokValue Var         str = cast str
  tokValue Mu          str = ()
  tokValue (BinOp o)   str = str
  tokValue (Punct p)   str = ()
  tokValue Whitespace  str = ()

Eq TypeKind where
  (==) Ident      Ident      = True
  (==) PrimType   PrimType   = True
  (==) Var        Var        = True
  (==) Mu         Mu         = True
  (==) (BinOp o1) (BinOp o2) = o1 == o2
  (==) (Punct p1) (Punct p2) = p1 == p2
  (==) Whitespace Whitespace = True
  (==) _          _          = False

Show TypeKind where
  show Ident      = "Ident"
  show PrimType   = "PrimType"
  show Var        = "Var"
  show Mu         = "Mu"
  show (BinOp x)  = "BinOp"
  show (Punct x)  = "Punct"
  show Whitespace = "Whitespace"

TypeToken : Type
TypeToken = Token TypeKind
