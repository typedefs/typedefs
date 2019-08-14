module DSL

import Typedefs


data SyntaxDef : Type where
  Zero : SyntaxDef
  One : SyntaxDef
  -- a reference to an existing type
  Identifier : String -> SyntaxDef
  -- a definition of a new tdef
  Constructor : String -> SyntaxDef -> SyntaxDef
  -- a + b
  InfixPlus : SyntaxDef -> SyntaxDef -> SyntaxDef
  -- a * b
  InfixTimes : SyntaxDef -> SyntaxDef -> SyntaxDef
  -- a * x
  InfixPower : SyntaxDef -> Int -> SyntaxDef

  -- t a
  App : SyntaxDef -> SyntaxDef -> SyntaxDef

record NamedDef where
  constructor MkNamedDef
  Name : String
  Args : List String
  Def  : SyntaxDef


infixr 0 :=

interface Assignable t where
  (:=) : t -> SyntaxDef -> NamedDef

Assignable String where
  (:=) name def = MkNamedDef name [] def
Assignable (String, List String) where
  (:=) (name, args) def = MkNamedDef name args def


infixr 5 ^

(^) : SyntaxDef -> Int -> SyntaxDef
(^) def n = InfixPower def n
syntax [a]"'" = Identifier a
syntax [a]":" [b] = Constructor a b

natToDef : Nat -> SyntaxDef
natToDef Z = Zero
natToDef (S Z) = One
natToDef (S k) = InfixPlus One (natToDef k)


Num SyntaxDef where
  (+) x y = InfixPlus x y
  (*) x y = InfixTimes x y
  fromInteger n = natToDef $ toNat n

Show SyntaxDef where
  show Zero = "0"
  show One = "1"
  show (Identifier x) = x
  show (Constructor x y) = x ++ " : " ++ show y
  show (InfixPlus x y) = show x ++ " | " ++ show y
  show (InfixTimes x y) = show x ++ " * " ++ show y
  show (InfixPower x y) = show x ++ " ^ " ++ show y
  show (App t a) = show t ++ " " ++ show a

Show NamedDef where
  show (MkNamedDef n args def) = n ++ " " ++ unwords args ++ " := " ++ show def


(||) : SyntaxDef -> SyntaxDef -> SyntaxDef
(||) = InfixPlus


boolTest : NamedDef
boolTest = "bool" := 1 || 1

eitherTest : NamedDef
eitherTest = ("either", ["a", "b"]) := ("Left" : "a"') || ("Right" : "b"')


bytesTest : NamedDef
bytesTest = "bytes" := "bool"' ^ 8

listTest : NamedDef
listTest = ("List", ["a"]) := 1 || "a"' * App ("List"') 1
