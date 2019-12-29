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

-- Show instances

mutual
  Show Power where
    show (PLit k) = show k
    show (PEmb x) = show x

  Show Factor where
    show (FEmb x) = show x
    show (FPow x y) = show x ++ " ^ " ++ show y

  Show Term where
    show (TEmb x) = show x
    show (TMul x y) = show x ++ " * " ++ show y

  Show Expr where
    show (EEmb x) = show x
    show (ESum x y) = show x ++ " + " ++ show y
    show (Ref x) =  x

Show Definition where
  show (Simple x) = show x
  show (Enum xs) = unwords $ intersperse "|" (map (\(dcon, tpe) => dcon ++ " : " ++ show tpe) xs)
  show (Record xs) = ?Show_rhs_4

Show DefName where
  show (MkDefName name []) = name
  show (MkDefName name arguments) = name ++ " " ++ unwords arguments

export
Show TopLevelDef where
  show (MkTopLevelDef name def) = show name ++ " := " ++ show def

-- Eq instances

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


Eq TopLevelDef where
  (==) (MkTopLevelDef nl dl) (MkTopLevelDef nr dr) = nl == nr && dl == dr
