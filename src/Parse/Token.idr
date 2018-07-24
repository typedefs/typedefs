module Parse.Token

import Text.Lexer

%default total
%access public export

-- two n-ary operations
data NOpType = SumNO | ProdNO

Eq NOpType where
  (==) SumNO  SumNO  = True
  (==) ProdNO ProdNO = True
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
  | NOp NOpType
  | Punct ParenType
  | Number
  | Whitespace

TokenKind TypeKind where
  TokType t = case t of
    Ident         => String
    PrimType      => String
    Var           => Unit
    Mu            => Unit
    (NOp o)       => String
    (Punct p)     => Unit
    Number        => Nat
    Whitespace    => Unit

  tokValue t str = case t of
    Ident        => str
    PrimType     => str
    Var          => ()
    Mu           => ()
    (NOp o)      => str
    (Punct p)    => ()
    Number       => cast str
    Whitespace   => ()

Eq TypeKind where
  (==) Ident      Ident      = True
  (==) PrimType   PrimType   = True
  (==) Var        Var        = True
  (==) Mu         Mu         = True
  (==) (NOp o1)   (NOp o2)   = o1 == o2
  (==) (Punct p1) (Punct p2) = p1 == p2
  (==) Whitespace Whitespace = True
  (==) Number     Number     = True
  (==) _          _          = False

Show TypeKind where
  show Ident      = "Ident"
  show PrimType   = "PrimType"
  show Var        = "Var"
  show Mu         = "Mu"
  show (NOp x)    = "NOp"
  show (Punct x)  = "Punct"
  show Whitespace = "Whitespace"
  show Number     = "Number"

TypeToken : Type
TypeToken = Token TypeKind

-- for debug

Show k => Show (Token k) where
  show (Tok k t) = "Token '" ++ t ++ "':" ++ show k

Show a => Show (TokenData a) where
  show (MkToken l c a) = "TokenData l:" ++ show l ++ " c:" ++ show c ++ " " ++ show a