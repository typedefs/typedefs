import Data.Vect
import Data.Fin

import Types
import Typedefs
import TermWrite
import Backend.Haskell

------ example: bits -

bit : TDef Z
bit = TSum [T1, T1]

byte : TDef Z
byte = pow 8 bit

test : Type
test = Ty [] bit

----- example: maybe -

maybe : TDef 1
maybe = TSum [T1, TVar 0]

nothing : (a : Type) -> Ty [a] Main.maybe
nothing _ = Left ()

just : (a : Type) -> a -> Ty [a] Main.maybe
just a = Right

----- example: list --

||| `TDef 1` means the `list` type we're defining contains 1 type variable
list : TDef 1
list = TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

||| The `Ty` function applied in the result type takes a typedef and constructs
||| a corresponding Idris type. In this example, the typedef is `list : TDef 1`,
||| and the corresponding Idris type is a cons-list of `a`-elements. In order to
||| construct a value of this type - in this case the empty list `nil` - we need
||| to fix (i.e. choose) an Idris type `a`. We do so in the form of the `a :
||| Type` parameter. That's all the info we need to construct an empty list of
||| `a`s.
|||
||| @a The (Idris-side) element type of the list to construct
nil : (a : Type) -> Ty [a] Main.list
nil x = Inn $ Left ()

||| Like `nil`, but we construct a new, non-empty list by taking an existing
||| list `xs` (which may or may not be empty) and prepending a new head element
||| `x`.
|||
||| @a the (Idris-side) type of elements of the list to construct
||| @x the head of the list to construct
||| @xs the tail of the list to construct
cons : (a : Type) -> (x : a) -> (xs : Ty [a] Main.list) -> Ty [a] Main.list
cons a x xs = Inn $ Right (x, xs)

-- Example: Maybe

maybe2 : TDef 1
maybe2 = TMu "Maybe" [("Nothing", T1), ("Just", TVar 1)]

nothing2 : (a : Type) -> Ty [a] Main.maybe2
nothing2 a = Inn (Left ())

just2 : (a : Type) -> a -> Ty [a] Main.maybe2
just2 a x = Inn (Right x)

-- Example: List Nat

listNat : TDef 0
listNat = TMu "ListNat" [("NilN", T1), ("ConsN", TProd [nat, TVar 0])]
  where
  nat : TDef 1
  nat = TMu "Nat" [("ZZ", T1), ("SS", TVar 0)]

listNat2 : TDef 0
listNat2 = TMu "ListNat" [("NilN", T1), ("ConsN", TProd [nat, nat, TVar 0])]
  where
  nat : TDef 1
  nat = TMu "Nat" [("ZZ", T1), ("SS", TVar 0)]

serializeTest : String
serializeTest = serialize [Int] [show] Main.maybe (Main.just Int 6)

main : IO ()
main = do
     putStrLn $ showTDef Main.list
