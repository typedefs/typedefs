import Data.Vect
import Data.Fin

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.TermWrite
import Typedefs.Backend.Haskell
import Typedefs.Backend.ReasonML

-- Example: bits

bit : TDefR Z
bit = TSum [T1, T1]

byte : TDefR Z
byte = pow 8 bit

test : Type
test = Ty [] bit

-- Example: maybe

maybe : TDefR 1
maybe = TSum [T1, TVar 0]

nothing : (a : Type) -> Ty [a] Main.maybe
nothing _ = Left ()

just : (a : Type) -> a -> Ty [a] Main.maybe
just a = Right

maybe2 : TNamedR 1
maybe2 = TName "Maybe" $ TMu [("Nothing", T1), ("Just", TVar 1)]

nothing2 : (a : Type) -> Ty [a] (def Main.maybe2)
nothing2 a = Inn (Left ())

just2 : (a : Type) -> a -> Ty [a] (def Main.maybe2)
just2 a x = Inn (Right x)

-- Example: either

either : TDefR 2
either = TSum [TVar 0, TVar 1]

left : {a : Type} -> {b : Type} -> a -> Ty [a,b] Main.either
left a = Left a

right : {a : Type} -> {b : Type} -> b -> Ty [a,b] Main.either
right b = Right b

either2 : TNamedR 2
either2 = TName "Either" $ TMu [("Left", TVar 1), ("Right", TVar 2)]

left2 : {a : Type} -> {b : Type} -> a -> Ty [a,b] (def Main.either2)
left2 x = Inn (Left x)

right2 : {a : Type} -> {b : Type} -> b -> Ty [a,b] (def Main.either2)
right2 x = Inn (Right x)

-- Example: list

%hide list

||| `TDefR 1` means the `list` type we're defining contains 1 type variable
list : TNamedR 1
list = TName "List" $ TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

||| The `Ty` function applied in the result type takes a typedef and constructs
||| a corresponding Idris type. In this example, the typedef is `list : TDefR 1`,
||| and the corresponding Idris type is a cons-list of `a`-elements. In order to
||| construct a value of this type - in this case the empty list `nil` - we need
||| to fix (i.e. choose) an Idris type `a`. We do so in the form of the `a :
||| Type` parameter. That's all the info we need to construct an empty list of
||| `a`s.
|||
||| @a The (Idris-side) element type of the list to construct
nil : (a : Type) -> Ty [a] (def Main.list)
nil x = Inn $ Left ()

||| Like `nil`, but we construct a new, non-empty list by taking an existing
||| list `xs` (which may or may not be empty) and prepending a new head element
||| `x`.
|||
||| @a the (Idris-side) type of elements of the list to construct
||| @x the head of the list to construct
||| @xs the tail of the list to construct
cons : (a : Type) -> (x : a) -> (xs : Ty [a] (def Main.list)) -> Ty [a] (def Main.list)
cons a x xs = Inn $ Right (x, xs)

-- Example: List Nat

nat : TNamedR 0
nat = TName "Nat" $ TMu [("ZZ", T1), ("SS", TVar 0)]

nat1 : TDefR 1
nat1 = weakenTDef (def nat) 1 LTEZero

listNat : TNamedR 0
listNat = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [nat1, TVar 0])]

listNat2 : TNamedR 0
listNat2 = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [nat1, nat1, TVar 0])]

-- Examples using `ap`

maybeEitherAlpha : TDefR 1
maybeEitherAlpha = maybe `ap` [either `ap` [TVar 0, TVar 0]]

maybeEitherAlphaBeta : TDefR 2
maybeEitherAlphaBeta = maybe `ap` [either `ap` [TVar 0, TVar 1]]

nullBit : TDefR 0
nullBit = maybe `ap` [bit]

listEitherAlpha : TDefR 1
listEitherAlpha = (def list) `ap` [either `ap` [TVar 0, TVar 0]]

listEitherAlphaBeta : TDefR 2
listEitherAlphaBeta = (def list) `ap` [either `ap` [TVar 0, TVar 1]]

listBit : TDefR 0
listBit = (def list) `ap` [bit]

listNullBit : TDefR 0
listNullBit = (def list) `ap` [nullBit]

nestedMu : TNamedR 0
nestedMu = TName "Foo" $ TMu [("Bar", nat1)]

serializeTest : String
serializeTest = serialize [Int] [show] Main.maybe (Main.just Int 6)

main : IO ()
main = do
     putStrLn $ showTDef (def Main.list)
