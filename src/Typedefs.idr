module Typedefs

import Data.Fin
import Data.Vect
import Types

%default total

%access public

export

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
