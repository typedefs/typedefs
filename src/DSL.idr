module DSL

import Typedefs


data SyntaxDef : Type where
  Zero : SyntaxDef
  One : SyntaxDef
  -- a reference to an existing type
  Identifier : String -> SyntaxDef
  -- a definition of a new tdef
  NameDef : String -> List String -> SyntaxDef -> SyntaxDef
  -- a + b
  InfixPlus : SyntaxDef -> SyntaxDef -> SyntaxDef
  -- a * b
  InfixTimes : SyntaxDef -> SyntaxDef -> SyntaxDef
  -- a * x
  InfixPower : SyntaxDef -> Int -> SyntaxDef

  -- t a
  App : SyntaxDef -> SyntaxDef -> SyntaxDef

infixr 0 :=

interface Assignable t where
  (:=) : t -> SyntaxDef -> SyntaxDef

Assignable String where
  (:=) name def = NameDef name [] def
Assignable (String, List String) where
  (:=) (name, args) def = NameDef name args def

infixr 5 ^

(^) : SyntaxDef -> Int -> SyntaxDef
(^) def n = InfixPower def n
syntax [a]"'" = Identifier a

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
  show (NameDef x xs y) = x ++ " " ++ unwords xs ++ " := " ++ show y
  show (InfixPlus x y) = show x ++ " + " ++ show y
  show (InfixTimes x y) = show x ++ " * " ++ show y
  show (InfixPower x y) = show x ++ " ^ " ++ show y
  show (App t a) = show t ++ " " ++ show a

(<*>) : (f : SyntaxDef) -> SyntaxDef -> SyntaxDef
(<*>) f a = App f a

pure : SyntaxDef -> SyntaxDef
pure = id

boolTest : SyntaxDef
boolTest = "bool" := 1 + 1

eitherTest : SyntaxDef
eitherTest = ("either", ["a", "b"]) := ("left" := "a"') + ("right" := "b"')


bytesTest : SyntaxDef
bytesTest = "bytes" := "bool"' ^ 8

listTest : SyntaxDef
listTest = ("list", ["a"]) := 1 + "a"' * App ("list"') 1
