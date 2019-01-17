module Typedefs

import Data.Fin
import Data.Vect

import Types

%default total
%access public export

mutual
  ||| Type definition
  ||| @n The number of type variables in the type
  data TDef : (n:Nat) -> Type where
    ||| The empty type
    T0    :                                      TDef n

    ||| The unit type
    T1    :                                      TDef n

    ||| The coproduct type
    TSum  :         Vect (2 + k) (TDef n)     -> TDef n

    ||| The product type
    TProd :         Vect (2 + k) (TDef n)     -> TDef n

    ||| A type variable
    ||| @i De Bruijn index
    TVar  :         (i:Fin (S n))             -> TDef (S n)

    ||| Mu
    TMu   :         Vect k (Name, TDef (S n)) -> TDef n
--
--    TName : Name -> TDef n                    -> TDef n

    TApp  : TNamed k -> Vect k (TDef n)       -> TDef n

  data TNamed : (n : Nat) -> Type where
    TName : Name -> TDef n -> TNamed n

name : TNamed n -> Name
name (TName n _) = n

td : TNamed n -> TDef n
td (TName _ t) = t

arity : TDef n -> Nat
arity {n} _ = n

idVars : Vect n (TDef n)
idVars {n} with (n)
  idVars | Z     = []
  idVars | (S _) = map TVar range

alias : Name -> TNamed n -> TNamed n
alias name tn = TName name (TApp tn idVars)

||| Add 1 to all de Bruijn-indices in a TDef.
shiftVars : TDef n -> TDef (S n)
shiftVars T0             = T0
shiftVars T1             = T1
shiftVars (TSum ts)      = assert_total $ TSum $ map shiftVars ts
shiftVars (TProd ts)     = assert_total $ TProd $ map shiftVars ts
shiftVars (TVar v)       = TVar $ shift 1 v
--shiftVars (TName name t) = assert_total $ TName name $ shiftVars t
shiftVars (TMu cs)       = assert_total $ TMu $ map (map shiftVars) cs
shiftVars (TApp f xs)    = ?shiftTApp

||| Apply a TDef with free variables to a vector of arguments.
ap : TDef n -> Vect n (TDef m) -> TDef m
ap T0             _    = T0
ap T1             _    = T1
ap (TSum ts)      args = assert_total $ TSum $ map (flip ap args) ts
ap (TProd ts)     args = assert_total $ TProd $ map (flip ap args) ts
ap (TVar v)       args = index v args
--ap (TName name t) args = TName name $ ap t args
ap (TMu cs)       args = assert_total $ TMu $ map (map (flip ap (TVar 0 :: map shiftVars args))) cs
ap (TApp f xs)    args = ?ap_TApp

mutual
  data Mu : Vect n Type -> TDef (S n) -> Type where
    Inn : Ty (Mu tvars m :: tvars) m -> Mu tvars m

  args : Vect k (String, TDef (S n)) -> TDef (S n)
  args []                 = T0
  args [(_,m)]            = m
  args ((_,m)::(_,l)::ms) = TSum (m :: l :: map snd ms)

  Tnary : Vect n Type -> Vect (2 + k) (TDef n) -> (Type -> Type -> Type) -> Type   
  Tnary tvars [x, y]              c = c (Ty tvars x) (Ty tvars y)
  Tnary tvars (x :: y :: z :: zs) c = c (Ty tvars x) (Tnary tvars (y :: z :: zs) c)

  ||| Interpret a type definition as an Idris `Type`. In `tvars : Vect n`, we
  ||| need to provide an Idris type for each of the `n` type variables in the
  ||| typedef. The De Bruijn indices in the `TVar`s in this typedef will be
  ||| mapped onto (i.e. instantiated at) the Idris types in `tvars`.
  Ty : Vect n Type -> TDef n -> Type
  Ty     tvars T0          = Void
  Ty     tvars T1          = Unit
  Ty {n} tvars (TSum xs)   = Tnary tvars xs Either 
  Ty {n} tvars (TProd xs)  = Tnary tvars xs Pair
  Ty     tvars (TVar v)    = Vect.index v tvars
  Ty     tvars (TMu m)     = Mu tvars (args m)
  --Ty     tvars (TName _ t) = Ty tvars t
  Ty     tvars (TApp f xs) = ?TyTApp

------ meta ----------

pow : Nat -> TDef n -> TDef n
pow Z         _ = T1
pow (S Z)     a = a
pow (S (S n)) a = TProd (a :: a :: replicate n a)

powN : Nat -> TNamed n -> TDef n
powN n tn = pow n (TApp tn idVars)

-- TODO add to stdlib?
minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     m    _   = rewrite plusZeroRightNeutral (m `minus` 0) in
                            minusZeroRight m
minusPlus (S _)  Z    lte = absurd lte
minusPlus (S n) (S m) lte = rewrite sym $ plusSuccRightSucc (m `minus` n) n in
                            cong $ minusPlus n m (fromLteSucc lte)

mutual
  ||| Increase the type index representing the number of variables accessible
  ||| to a `TDef`, without actually changing the variables that are used by it.
  |||
  ||| @m The new amount of variables.
  weakenTDef : TDef n -> (m : Nat) -> LTE n m -> TDef m
  weakenTDef T0             _    _   = T0
  weakenTDef T1             _    _   = T1
  weakenTDef (TSum xs)      m    prf = TSum $ weakenTDefs xs m prf
  weakenTDef (TProd xs)     m    prf = TProd $ weakenTDefs xs m prf
  weakenTDef (TVar _)       Z    prf = absurd prf
  weakenTDef (TVar {n} i)  (S m) prf =
    let prf' = fromLteSucc prf in
    rewrite sym $ minusPlus n m prf' in
    rewrite plusCommutative (m `minus` n) n in
    TVar $ weakenN (m-n) i
  weakenTDef (TMu xs)   m    prf =
    TMu $ weakenNTDefs xs (S m) (LTESucc prf)
  --weakenTDef (TName nam x)   m    prf =
  --TName nam $ weakenTDef x m prf
  weakenTDef (TApp f xs)    m    prf = ?weakenTApp

  weakenTDefs : Vect k (TDef n) -> (m : Nat) -> LTE n m -> Vect k (TDef m)
  weakenTDefs []      _ _   = []
  weakenTDefs (x::xs) m lte = weakenTDef x m lte :: weakenTDefs xs m lte

  weakenNTDefs : Vect k (Name, TDef n) -> (m : Nat) -> LTE n m -> Vect k (Name, TDef m)
  weakenNTDefs []          _ _   = []
  weakenNTDefs ((n,x)::xs) m lte = (n, weakenTDef x m lte) :: weakenNTDefs xs m lte

-------- printing -------

parens : String -> String
parens "" = ""
parens s = "(" ++ s ++ ")"

curly : String -> String
curly "" = ""
curly s = "{" ++ s ++ "}"

square : String -> String
square "" = ""
square s = "[" ++ s ++ "]"

mutual
  showTDef : TDef n -> String
  showTDef T0         = "0"
  showTDef T1         = "1"
  showTDef (TSum xs)  = parens $ showOp "+" xs
  showTDef (TProd xs) = parens $ showOp "*" xs
  showTDef (TVar x)   = curly $ show $ toNat x
  showTDef (TMu ms)   = parens $ "mu " ++ square (showNTDefs ms)
  --showTDef (TName n x) = n ++ " " ++ square (showTDef x)
  showTDef (TApp f xs) = ?showTApp

  showOp : String -> Vect k (TDef n) -> String
  showOp _  []         = ""
  showOp _  [x]        = showTDef x
  showOp op (x::y::ys) = showTDef x ++ " " ++ op ++ " " ++ showOp op (y::ys)

  showNTDefs : Vect k (Name, TDef n) -> String
  showNTDefs []          = ""
  showNTDefs [(n,x)]     = n ++ ": " ++ showTDef x
  showNTDefs ((n,x)::xs) = n ++ ": " ++ showTDef x ++ ", " ++ showNTDefs xs

Show (TDef n) where
  show = showTDef

-- Equality -----

vectEq : Eq a => Vect n a -> Vect m a -> Bool
vectEq []      []      = True
vectEq (x::xs) (y::ys) = x == y && vectEq xs ys
vectEq _       _       = False

implementation Eq (TDef n) where
  T0            == T0              = True
  T1            == T1              = True
  (TSum xs)     == (TSum xs')      = assert_total $ vectEq xs xs'
  (TProd xs)    == (TProd xs')     = assert_total $ vectEq xs xs'
  (TVar i)      == (TVar i')       = i == i'
  (TMu xs)      == (TMu xs')       = assert_total $ vectEq xs xs'
--  (TName nam t) == (TName nam' t') = nam == nam' && t == t'
  (TApp f xs)   == (TApp f' xs')   = ?eqTApp
  _             == _               = False
