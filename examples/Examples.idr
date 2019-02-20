import Data.Vect
import Data.Fin

import Types
import Typedefs
import TermWrite
import Backend.Haskell
import Backend.ReasonML

-- Example: bits

bit : TDef Z
bit = TSum [T1, T1]

byte : TDef Z
byte = pow 8 bit

test : Type
test = Ty [] bit

-- Example: maybe

maybe : TDef 1
maybe = TSum [T1, TVar 0]

nothing : (a : Type) -> Ty [a] Main.maybe
nothing _ = Left ()

just : (a : Type) -> a -> Ty [a] Main.maybe
just a = Right

maybe2 : TNamed 1
maybe2 = TName "Maybe" $ TMu [("Nothing", T1), ("Just", TVar 1)]

nothing2 : (a : Type) -> Ty [a] (td Main.maybe2)
nothing2 a = Inn (Left ())

just2 : (a : Type) -> a -> Ty [a] (td Main.maybe2)
just2 a x = Inn (Right x)

-- Example: either

either : TDef 2
either = TSum [TVar 0, TVar 1]

left : {a : Type} -> {b : Type} -> a -> Ty [a,b] Main.either
left a = Left a

right : {a : Type} -> {b : Type} -> b -> Ty [a,b] Main.either
right b = Right b

either2 : TNamed 2
either2 = TName "Either" $ TMu [("Left", TVar 1), ("Right", TVar 2)]

left2 : {a : Type} -> {b : Type} -> a -> Ty [a,b] (td Main.either2)
left2 x = Inn (Left x)

right2 : {a : Type} -> {b : Type} -> b -> Ty [a,b] (td Main.either2)
right2 x = Inn (Right x)

-- Example: list

%hide list

||| `TDef 1` means the `list` type we're defining contains 1 type variable
list : TNamed 1
list = TName "List" $ TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

||| The `Ty` function applied in the result type takes a typedef and constructs
||| a corresponding Idris type. In this example, the typedef is `list : TDef 1`,
||| and the corresponding Idris type is a cons-list of `a`-elements. In order to
||| construct a value of this type - in this case the empty list `nil` - we need
||| to fix (i.e. choose) an Idris type `a`. We do so in the form of the `a :
||| Type` parameter. That's all the info we need to construct an empty list of
||| `a`s.
|||
||| @a The (Idris-side) element type of the list to construct
nil : (a : Type) -> Ty [a] (td Main.list)
nil x = Inn $ Left ()

||| Like `nil`, but we construct a new, non-empty list by taking an existing
||| list `xs` (which may or may not be empty) and prepending a new head element
||| `x`.
|||
||| @a the (Idris-side) type of elements of the list to construct
||| @x the head of the list to construct
||| @xs the tail of the list to construct
cons : (a : Type) -> (x : a) -> (xs : Ty [a] (td Main.list)) -> Ty [a] (td Main.list)
cons a x xs = Inn $ Right (x, xs)

-- Example: List Nat

nat : TNamed 0
nat = TName "Nat" $ TMu [("ZZ", T1), ("SS", TVar 0)]

nat1 : TDef 1
nat1 = weakenTDef (td nat) 1 LTEZero

listNat : TNamed 0
listNat = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [nat1, TVar 0])]

listNat2 : TNamed 0
listNat2 = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [nat1, nat1, TVar 0])]

-- Examples using `ap`

maybeEitherAlpha : TDef 1
maybeEitherAlpha = maybe `ap` [either `ap` [TVar 0, TVar 0]]

maybeEitherAlphaBeta : TDef 2
maybeEitherAlphaBeta = maybe `ap` [either `ap` [TVar 0, TVar 1]]

nullBit : TDef 0
nullBit = maybe `ap` [bit]

listEitherAlpha : TDef 1
listEitherAlpha = (td list) `ap` [either `ap` [TVar 0, TVar 0]]

listEitherAlphaBeta : TDef 2
listEitherAlphaBeta = (td list) `ap` [either `ap` [TVar 0, TVar 1]]

listBit : TDef 0
listBit = (td list) `ap` [bit]

listNullBit : TDef 0
listNullBit = (td list) `ap` [nullBit]

nestedMu : TNamed 0
nestedMu = TName "Foo" $ TMu [("Bar", nat1)]

serializeTest : String
serializeTest = serialize [Int] [show] Main.maybe (Main.just Int 6)

main : IO ()
main = do
     putStrLn $ showTDef (td Main.list)
