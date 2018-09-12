module Typedefs

import Data.Fin
import Data.Vect
import Types

%default total

%access public

export

||| Type definition
||| @n The number of type variables in the type
data TDef : (n:Nat) -> Type where
  ||| The empty type
  T0 :                                         TDef n

  ||| The unit type
  T1 :                                         TDef n

  ||| The coproduct type
  TSum :            Vect (2 + k) (TDef n)   -> TDef n

  ||| The product type
  TProd :           Vect (2 + k) (TDef n)   -> TDef n

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
  Ty     tvars T0         = Void
  Ty     tvars T1         = Unit
  Ty {n} tvars (TSum xs)  = tsum xs
    where
    tsum : Vect (2 + _) (TDef n) -> Type
    tsum [x, y]              = Either (Ty tvars x) (Ty tvars y)
    tsum (x :: y :: z :: zs) = Either (Ty tvars x) (tsum (y :: z :: zs))
  Ty {n} tvars (TProd xs) = tprod xs
    where
    tprod : Vect (2 + _) (TDef n) -> Type
    tprod [x, y]              = Pair (Ty tvars x) (Ty tvars y)
    tprod (x :: y :: z :: zs) = Pair (Ty tvars x) (tprod (y :: z :: zs))
  Ty     tvars (TVar v)   = Vect.index v tvars
  Ty     tvars (TMu _ m)  = Mu tvars (args m)
    where
    args []                 = T0
    args [(_,m)]            = m
    args ((_,m)::(_,l)::ms) = TSum (m :: l :: map snd (fromList ms))

------ meta ----------

pow : Nat -> TDef n -> TDef n
pow Z         _ = T1
pow (S Z)     a = a
pow (S (S n)) a = TProd (a :: a :: replicate n a)

------- compile to Idris ? -----

defType : String -> String -> String
defType name def = name ++ " : Type\n" ++ name ++ " = " ++ def

compileClosed : TDef n -> String
compileClosed T0         = "Void"
compileClosed T1         = "Unit"
compileClosed (TSum xs)  = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "Either (" ++ compileClosed x ++ ") (" ++ compileClosed y ++ ")"
  tsum (x :: y :: z :: zs) = "Either (" ++ compileClosed x ++ ") (" ++ tsum (y :: z :: zs) ++ ")"
compileClosed (TProd xs) = tprod xs
  where
  tprod : Vect (2 + _) (TDef n) -> String
  tprod [x, y]              = "Pair (" ++ compileClosed x ++ ") (" ++ compileClosed y ++ ")"
  tprod (x :: y :: z :: zs) = "Pair (" ++ compileClosed x ++ ") (" ++ tprod (y :: z :: zs) ++ ")"
compileClosed (TMu _ x)  = "TMu: nope"
compileClosed (TVar x)   = "TVar: nope"

-------- printing -------

parens : String -> String
parens s = "(" ++ s ++ ")"

curly : String -> String
curly s = "{" ++ s ++ "}"

square : String -> String
square s = "[" ++ s ++ "]"

mutual
  showTDef : TDef n -> String
  showTDef T0         = "0"
  showTDef T1         = "1"
  showTDef (TSum xs)  = parens $ showOp "+" xs
  showTDef (TProd xs) = parens $ showOp "*" xs
  showTDef (TVar x)   = curly $ show $ toNat x
  showTDef (TMu n ms) = n ++ " = mu " ++ square (showNTDefs ms)

  showOp : String -> Vect k (TDef n) -> String
  showOp _  []         = ""
  showOp _  [x]        = showTDef x
  showOp op (x::y::ys) = showTDef x ++ " " ++ op ++ " " ++ showOp op (y::ys)

  showNTDefs : List (Name, TDef n) -> String
  showNTDefs []          = ""
  showNTDefs [(n,x)]     = n ++ ": " ++ showTDef x
  showNTDefs ((n,x)::xs) = n ++ ": " ++ showTDef x ++ ", " ++ showNTDefs xs

Show (TDef n) where
  show = showTDef
