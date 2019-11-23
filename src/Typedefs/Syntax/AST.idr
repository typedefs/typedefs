module Typedefs.Syntax.AST

%access public export

mutual
  data Expr = EEmb Term
            | ESum Expr Term
            | Ref String

  -- Weak priority
  data Term : Type where
    TEmb : Factor -> Term
    TMul : Term -> Factor -> Term

  -- Strong priority
  data Factor : Type where
    FEmb : Power -> Factor
    FPow : Factor -> Power -> Factor

  -- Strongest priority
  data Power : Type where
    PLit : Nat -> Power
    PEmb : Factor -> Power


record DefName where
  constructor MkDefName
  name      : String
  arguments : List String

data Definition
  = Simple Expr
  | Enum   (List (String, Expr))
  | Record (List (String, Expr))

record TopLevelDef where
  constructor MkTopLevelDef
  name : DefName
  def  : Definition
