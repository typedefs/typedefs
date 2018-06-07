module Token

import Text.Lexer

%default total
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
  | Number
  | Whitespace

TokenKind TypeKind where
  TokType t = case t of
    Ident         => String
    PrimType      => String
    Var           => Unit
    Mu            => Unit
    (BinOp o)     => String
    (Punct p)     => Unit
    Number        => Nat
    Whitespace    => Unit

  tokValue t str = case t of
    Ident        => str
    PrimType     => str
    Var          => ()
    Mu           => ()
    (BinOp o)    => str
    (Punct p)    => ()
    Number       => cast str
    Whitespace   => ()

Eq TypeKind where
  (==) Ident      Ident      = True
  (==) PrimType   PrimType   = True
  (==) Var        Var        = True
  (==) Mu         Mu         = True
  (==) (BinOp o1) (BinOp o2) = o1 == o2
  (==) (Punct p1) (Punct p2) = p1 == p2
  (==) Whitespace Whitespace = True
  (==) Number     Number     = True
  (==) _          _          = False

Show TypeKind where
  show Ident      = "Ident"
  show PrimType   = "PrimType"
  show Var        = "Var"
  show Mu         = "Mu"
  show (BinOp x)  = "BinOp"
  show (Punct x)  = "Punct"
  show Whitespace = "Whitespace"
  show Number     = "Number"

TypeToken : Type
TypeToken = Token TypeKind
