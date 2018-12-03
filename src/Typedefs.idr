module Typedefs

import Data.Fin
import Data.Vect
import Data.HVect
import Language.Reflection

import Types

%default total
%access public export
%language ElabReflection

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

  TRec  : Name -> Vect (2 + k) (Name, TDef n) -> TDef n

  ||| A type variable
  ||| @i De Bruijn index
  TVar  :         (i:Fin (S n))             -> TDef (S n)

  ||| Mu
  TMu   : Name -> Vect k (Name, TDef (S n)) -> TDef n

  TName : Name -> TDef n                    -> TDef n

data Record : Vect n (Name, Type) -> Type where
  Nil : Record []
  Cons : (n : Name) -> t -> Record r -> Record ((n, t) :: r)

get : (n : Name) -> Record fields -> {auto p: Elem (n,t) fields} -> t
get _ (Cons _ v _) {p=Here}    = v
get n (Cons _ _ r) {p=There q} = get n r {p=q}



--getRec : {t: Type} -> Name -> HVect ts -> Elem (StrM ) -> t
--getRec {t} n r = snd $ get {ts=} r
--recGet : {t: Type} -> (n : Name) -> RecordData fields -> {auto p: Elem (n,t) fields} -> t
--recGet {t} name r {p} = get r {p=?halp}

--recSet : {t: Type} -> Name -> RecordData fields -> t -> RecordData fields
--recSet {t} name r val = put (the (StrM name -> t) (const val)) r

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

  TList : Vect n Type -> Vect (2 + k) (TDef n) -> Vect (2 + k) Type
  TList tvars ts = map (Ty tvars) ts

--  Record : Vect n Type -> Vect (2 + k) (TDef n) -> Vect (2 + k) Type
--  Record tvars ts = map (Field . Ty tvars) ts
--    where
--
--    Getter : Type -> Type
--    Getter t = TList -> t
--
--    Setter : Type -> Type
--    Setter t = ts -> t -> ts
--
--    Field : Type -> Type
--    Field t = (t ** (Pair (Getter t) (Setter t)))

  ||| Interpret a type definition as an Idris `Type`. In `tvars : Vect n`, we
  ||| need to provide an Idris type for each of the `n` type variables in the
  ||| typedef. The De Bruijn indices in the `TVar`s in this typedef will be
  ||| mapped onto (i.e. instantiated at) the Idris types in `tvars`.
  Ty : Vect n Type -> TDef n -> Type
  Ty     tvars T0          = Void
  Ty     tvars T1          = Unit
  Ty {n} tvars (TSum xs)   = Tnary tvars xs Either 
  Ty {n} tvars (TProd xs)  = Tnary tvars xs Pair
  Ty     tvars (TRec _ xs) = ?halpme -- Record tvars (map snd xs)
  Ty     tvars (TVar v)    = Vect.index v tvars
  Ty     tvars (TMu _ m)   = Mu tvars (args m)
  Ty     tvars (TName _ t) = Ty tvars t

getTT : TDef 0 -> Raw
getTT T0 = `(Void)
getTT T1 = `(Unit)
--getTT (TSum [x,y]) = `(Either ~(getTT x) ~(getTT y))
--getTT (TSum (x :: y :: z :: xs)) = `(Either ~(getTT x) ~(getTT $ TSum (y::z::xs)))
--getTT (TProd [x,y]) = `(Pair ~(getTT x) ~(getTT y))
--getTT (TProd (x :: y :: z :: xs)) = `(Pair ~(getTT x) ~(getTT $ TProd (y::z::xs)))
getTT _ = ?getttttt

record School where
  constructor MkSchool
  schoolName : String
  classes : Nat
  open : Bool

mkAccessors : TTName -> List ConstructorDefn -> Elab ()
mkAccessors name cs = traverse_ (traverse_ mkAccessorss . arguments) cs
  where
  mkAccessorss : FunArg -> Elab ()
  mkAccessorss (MkFunArg fieldName fieldType _ _) = do
      declareType $ Declare fieldName [MkFunArg name (Var name) Explicit NotErased] fieldType
--      DefineFun _ clauses <- lookupFunDefnExact (NS (UN "classes") ["School", "Typedefs"])
      --?defineFun $ DefineFun fieldName [MkFunClause ?pattern ?body] -- Need access to entire constructor to create pattern match using a TT-expr

mkAccess : DataDefn -> Elab ()
mkAccess (DefineDatatype name cs) = ?lel
  where 
  mkAccessCons : ConstructorDefn -> Elab ()
  mkAccessCons cDef = --let consTT = Bind (name cDef)  in
    traverse_ mkAccessField (arguments cDef)
    where

    mkAccessField : FunArg -> Elab ()
    mkAccessField (MkFunArg fieldName fieldType _ _) = do
      declareType $ Declare fieldName [MkFunArg name (Var name) Explicit NotErased] fieldType
      defineFunction $ DefineFun fieldName [MkFunClause ?pattern ?body]

genRecord : String -> List (String, TDef 0) -> Elab ()
genRecord n fields =
  do recN <- inThisNS n
     declareDatatype $ Declare recN [] `(Type)
     let ctorN = UN ("Mk" ++ n)
     let tyDefn = DefineDatatype recN [
        Constructor ctorN
                    (map fieldArg fields)
                    (Var recN)
     ]
     defineDatatype tyDefn
--     mkAccessors recN (constructors tyDefn)
  where
  inThisNS : String -> Elab TTName
  inThisNS n = pure $ NS (UN n) !currentNamespace

  fieldArg : (String, TDef 0) -> FunArg
  fieldArg (fieldName, fieldType) = MkFunArg (UN fieldName) (getTT fieldType) Explicit NotErased


%runElab (genRecord "Student" [("age",T1)])

------ meta ----------
pow : Nat -> TDef n -> TDef n
pow Z         _ = T1
pow (S Z)     a = a
pow (S (S n)) a = TProd (a :: a :: replicate n a)

-- TODO add to stdlib?
minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     m    _   = rewrite plusZeroRightNeutral (m `minus` 0) in
                            minusZeroRight m
minusPlus (S _)  Z    lte = absurd lte
minusPlus (S n) (S m) lte = rewrite sym $ plusSuccRightSucc (m `minus` n) n in
                            cong $ minusPlus n m (fromLteSucc lte)

mutual
  weakenTDef : TDef n -> (m : Nat) -> LTE n m -> TDef m
  weakenTDef T0             _    _   = T0
  weakenTDef T1             _    _   = T1
  weakenTDef (TSum xs)      m    prf = TSum $ weakenTDefs xs m prf
  weakenTDef (TProd xs)     m    prf = TProd $ weakenTDefs xs m prf
  weakenTDef (TRec n xs)    m    prf = TRec n $ weakenNTDefs xs m prf
  weakenTDef (TVar _)       Z    prf = absurd prf
  weakenTDef (TVar {n} i)  (S m) prf =
    let prf' = fromLteSucc prf in
    rewrite sym $ minusPlus n m prf' in
    rewrite plusCommutative (m `minus` n) n in
    TVar $ weakenN (m-n) i
  weakenTDef (TMu nam xs)   m    prf =
    TMu nam $ weakenNTDefs xs (S m) (LTESucc prf)
  weakenTDef (TName nam x)   m    prf =
    TName nam $ weakenTDef x m prf

  weakenTDefs : Vect k (TDef n) -> (m : Nat) -> LTE n m -> Vect k (TDef m)
  weakenTDefs []      _ _   = []
  weakenTDefs (x::xs) m lte = weakenTDef x m lte :: weakenTDefs xs m lte

  weakenNTDefs : Vect k (Name, TDef n) -> (m : Nat) -> LTE n m -> Vect k (Name, TDef m)
  weakenNTDefs []          _ _   = []
  weakenNTDefs ((n,x)::xs) m lte = (n, weakenTDef x m lte) :: weakenNTDefs xs m lte

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
compileClosed (TRec n xs) = "TRec: nope"
compileClosed (TMu _ x)   = "TMu: nope"
compileClosed (TVar x)    = "TVar: nope"
compileClosed (TName n x) = "TName " ++ n ++ ": nope"

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
  showTDef (TRec n xs) = n ++ " = record " ++ square (showNTDefs xs)
  showTDef (TVar x)   = curly $ show $ toNat x
  showTDef (TMu n ms) = n ++ " = mu " ++ square (showNTDefs ms)
  showTDef (TName n x) = n ++ " " ++ square (showTDef x)

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
