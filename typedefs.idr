-- module Typedefs
import Data.Fin
import Data.Vect
import Types
import Parse

%default total

-- ||| @n The number of type variables in the type
data TDef : (n:Nat) -> Type where
  ||| The empty type
  T0 :                                         TDef n

  ||| The unit type
  T1 :                                         TDef n

  ||| The coproduct type
  TSum :  TDef n -> TDef n                  -> TDef n

  ||| The product type
  TProd : TDef n -> TDef n                  -> TDef n

  ||| A type variable
  ||| @i De Bruijn index
  TVar :            (i:Fin (S n))           -> TDef (S n)

  ||| Mu
  TMu :   Name   -> List (Name, TDef (S n)) -> TDef n

mutual
  data Mu : Vect n Type -> TDef (S n) -> Type where
    Inn : Ty (Mu tvars m :: tvars) m -> Mu tvars m

  ||| Interpret a type definition as an Idris `Type`. In `tvars : Vect n`, we
  ||| need to provide an Idris type for each of the `n` type variables in the
  ||| typedef. The De Bruijn indices in the `TVar`s in this typedef will be
  ||| mapped onto (i.e. instantiated at) the Idris types in `tvars`.
  Ty : Vect n Type -> TDef n -> Type
  Ty tvars T0          = Void
  Ty tvars T1          = Unit
  Ty tvars (TSum x y)  = Either (Ty tvars x) (Ty tvars y)
  Ty tvars (TProd x y) = Pair   (Ty tvars x) (Ty tvars y)
  Ty tvars (TVar v)    = Vect.index v tvars
  Ty tvars (TMu _ m)   = Mu tvars (args m)
    where args []          = T0
          args [(_,m)]     = m
          args ((_,m)::ms) = TSum m (args ms)

------ meta ----------

pow : Nat -> TDef n -> TDef n
pow Z _ = T1
pow (S n) a = TProd a (pow n a)

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

------- compile to Idris ? -----

defType : String -> String -> String
defType name def = name ++ " : Type\n" ++ name ++ " = " ++ def

compileClosed : TDef n -> String
compileClosed T0          = "Void"
compileClosed T1          = "Unit"
compileClosed (TSum x y)  = "Either (" ++ compileClosed x ++ ") (" ++ compileClosed y ++ ")"
compileClosed (TProd x y) = "Pair (" ++ compileClosed x ++ ") (" ++  compileClosed y ++ ")"
compileClosed (TMu _ x)   = "TMu: nope"
compileClosed (TVar x)    = "TVar: nope"

-------- printing -------

parens : String -> String
parens s = "(" ++ s ++ ")"

curly : String -> String
curly s = "{" ++ s ++ "}"

showOp : String -> String -> String -> String
showOp op x y = parens $ x ++ " " ++ op ++ " " ++ y

mutual
  showTDef : TDef n -> String
  showTDef T0          = "0"
  showTDef T1          = "1"
  showTDef (TSum x y)  = showOp "+" (showTDef x) (showTDef y)
  showTDef (TProd x y) = showOp "*" (showTDef x) (showTDef y)
  showTDef (TVar x)    = curly $ show $ toNat x
  showTDef (TMu n ms)  = n ++ " = mu [" ++ (showTDefs ms) ++ "]"

  showTDefs : List (Pair Name (TDef n)) -> String
  showTDefs []          = ""
  showTDefs [(n,x)]     = n ++ ": " ++ showTDef x
  showTDefs ((n,x)::xs) = n ++ ": " ++ showTDef x ++ ", " ++ showTDefs xs


main : IO ()
main = do
     putStrLn $ showTDef Main.list

     putStrLn ""
     Parse.testSuite

{-q
showTy x =
  case x of
    Ty0 => "0"
    Ty1 => "1"
    (a .+. b) => showOp "+" a b
    (a .*. b) => showOp "*" a b
  where
    parens : String -> String
    parens s = "(" ++ s ++ ")"
    showOp : String -> Ty -> Ty -> String
    showOp op x y = parens $ (showTy x) ++ " " ++ op ++ " " ++ (showTy y)
-}

-- interpreteren van type definities
--   tau : Ty -> Type
-- codec voor type definities
--   serialise : Ty -> Bits
--   deserialise : Bits -> Ty
-- codec voor termen van type
--   serialise : (t:Ty) -> x:(tau t) -> Bits
--   deserialise : Bits -> (t:Ty ** tau t)

-- prf (a .+. (b .+. c)) == ((a .+. b) .+. c)

-- prf Ty codec :
--   forall t:Ty. (serialise . deserialise) t == t

-- prf Term codec :
--   forall t:Ty. forall (x:tau t). (deserialise . serialise) t x == t

