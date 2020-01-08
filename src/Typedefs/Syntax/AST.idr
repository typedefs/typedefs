module Typedefs.Syntax.AST

import Data.NEList

%access public export

mutual
  -- Weakest priority
  data Appli : Type where
    AEmb : Expr -> Appli
    App : Appli -> Expr -> Appli

  -- Weaker priority
  data Expr = EEmb Term
            | ESum Expr Term

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
    PRef : String -> Power
    PEmb : Appli -> Power

record DefName where
  constructor MkDefName
  name      : String
  arguments : List String

data Definition
  = Simple Appli
  | Enum   (List (String, Appli))
  | Record (List (String, Appli))

record TopLevelDef where
  constructor MkTopLevelDef
  name : DefName
  def  : Definition

-- Show instances

mutual
  Show Appli where
    show (AEmb x) = show x
    show (App name arg) = show name ++ " " ++ show arg

  Show Power where
    show (PLit k) = show k
    show (PEmb x) = show x
    show (PRef x) = x

  Show Factor where
    show (FEmb x) = show x
    show (FPow x y) = show x ++ " ^ " ++ show y

  Show Term where
    show (TEmb x) = show x
    show (TMul x y) = show x ++ " * " ++ show y

  Show Expr where
    show (EEmb x) = show x
    show (ESum x y) = show x ++ " + " ++ show y

Show Definition where
  show (Simple x) = show x
  show (Enum xs) = unwords $ intersperse "|" (map (\(dcon, tpe) => dcon ++ " : " ++ show tpe) xs)
  show (Record xs) = "{" ++
                     (unwords $ intersperse "," (map (\(proj, tpe) => proj ++ " : " ++ show tpe) xs)) ++
                     "}"

Show DefName where
  show (MkDefName name []) = name
  show (MkDefName name argument) = name ++ " " ++ unwords argument

export
Show TopLevelDef where
  show (MkTopLevelDef name def) = show name ++ " := " ++ show def

-- Eq instances

Eq a => Eq (NEList a) where
  a == b = (NEList.toList a) == (NEList.toList b)

mutual
  Eq Appli where
    (==) (AEmb x ) (AEmb y ) = x == y
    (==) (App n a) (App m b) =
      n == m && a == b
    (==) _ _ = False

  Eq Power where
    (==) (PLit x) (PLit y) = x == y
    (==) (PEmb x) (PEmb y) = x == y
    (==) (PRef x) (PRef y) = x == y
    (==) _ _ = False

  Eq Factor where
    (==) (FEmb x  ) (FEmb y  ) = x == y
    (==) (FPow x z) (FPow y w) = x == y && z == w
    (==) _ _ = False

  Eq Term where
    (==) (TEmb x  ) (TEmb y  ) = x == y
    (==) (TMul x z) (TMul y w) = x == y && z == w
    (==) _ _ = False

  Eq Expr where
    (==) (EEmb x  ) (EEmb y  ) = x == y
    (==) (ESum x y) (ESum z w) = x == z && y == w
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
