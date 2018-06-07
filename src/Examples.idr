import Data.Vect
import Data.Fin
import Types
import Typedefs

------ example: bits -

bit : TDef Z
bit = TSum T1 T1

byte : TDef Z
byte = pow 8 bit

test : Type
test = Ty [] bit

----- example: maybe -

maybe : TDef 1
maybe = TSum T1 (TVar 0)

nothing : (A : Type) -> Ty [A] Main.maybe
nothing _ = Left ()

just : (A : Type) -> A -> Ty [A] Main.maybe
just A = Right

----- example: list --

||| `TDef 1` means the `list` type we're defining contains 1 type variable
list : TDef 1
list = TMu "list" ([("nil", T1), ("cons", TProd (TVar 1) (TVar 0))])

||| The `Ty` function applied in the result type takes a typedef and constructs
||| a corresponding Idris type. In this example, the typedef is `list : TDef 1`,
||| and the corresponding Idris type is a cons-list of `A`-elements. In order to
||| construct a value of this type - in this case the empty list `nil` - we need
||| to fix (i.e. choose) an Idris type `A`. We do so in the form of the `A :
||| Type` parameter. That's all the info we need to construct an empty list of
||| `A`s.
|||
||| @A The (Idris-side) element type of the list to construct
nil : (A : Type) -> Ty [A] Main.list
nil x = Inn $ Left ()

||| Like `nil`, but we construct a new, non-empty list by taking an existing
||| list `xs` (which may or may not be empty) and prepending a new head element
||| `x`.
|||
||| @A the (Idris-side) type of elements of the list to construct
||| @x the head of the list to construct
||| @xs the tail of the list to construct
cons : (A : Type) -> (x : A) -> (xs : Ty [A] Main.list) -> Ty [A] Main.list
cons A x xs = Inn $ Right (x, xs)


main : IO ()
main = do
     putStrLn $ showTDef Main.list
