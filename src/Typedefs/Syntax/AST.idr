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
    PEmb : Expr -> Power


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

mutual
  Eq Power where
    (==) (PLit x) (PLit y) = x == y
    (==) (PEmb x) (PEmb y) = x == y
    (==) _ _ = False

  Eq Factor where
    (==) (FEmb x) (FEmb y) = x == y
    (==) (FPow x y) (FPow z w) = x == z && y == w
    (==) _ _ = False

  Eq Term where
    (==) (TEmb x) (TEmb y) = x == y
    (==) (TMul x y) (TMul z w) = x == z && y == w
    (==) _ _ = False

  Eq Expr where
    (==) (EEmb x) (EEmb y) = x == y
    (==) (ESum x y) (ESum z w) = x == z && y == w
    (==) (Ref x) (Ref y) = x == y
    (==) _ _ = False

  Eq Definition where
    (==) (Simple x) (Simple y) = x == y
    (==) (Enum xs) (Enum ys) = xs == ys
    (==) (Record xs) (Record ys) = xs == ys
    (==) _ _ = False

Eq DefName where
  (==) (MkDefName nl al) (MkDefName nr ar) = nl == nr && al == ar

export
Show TopLevelDef where
  show v = ""

Eq TopLevelDef where
  (==) (MkTopLevelDef nl dl) (MkTopLevelDef nr dr) = nl == nr && dl == dr
