module Typedefs

import Data.Fin
import Data.Nat
import Data.Vect
import Data.List
import Data.List1
import Data.String

import public Typedefs.Names

%default total

mutual
  ||| Type definition
  ||| @n The number of type variables in the type
  ||| @b A flag to indicate whether the TDef contains unknown references
  public export
  data TDef' : (n : Nat) -> (b : Bool) -> Type where

    ||| The empty type
    T0    :
          -------------
            TDef' n b

    ||| The unit type
    T1    :
          -------------
            TDef' n b

    ||| The coproduct type
    TSum  : {k : Nat} ->
            Vect (2 + k) (TDef' n b) ->
          -------------------------------
            TDef' n b

    ||| The product type
    TProd : {k : Nat} ->
            Vect (2 + k) (TDef' n b) ->
          -------------------------------
            TDef' n b

    ||| A type variable
    ||| @i De Bruijn index
    TVar  : (i : Fin (S n)) ->
          ----------------------
            TDef' (S n) b

    ||| Mu
    TMu   : {k : Nat} ->
            Vect k (Name, TDef' (S n) b) ->
          ----------------------------------
            TDef' n b

    ||| Application of a named type to a vector of arguments.
    TApp  : {k : Nat} -> TNamed' k b -> Vect k (TDef' n b) -> TDef' n b

    ||| A resolved reference to an unknown typedef
    RRef  : Fin (S n) ->
          ---------------------
            TDef' (S n) False

    ||| A free reference to an unknown typedef
    FRef  : Name ->
          ----------------
            TDef' n True

  ||| Named type definition.
  ||| @n The number of type variables in the type.
  public export
  record TNamed' (n : Nat) (b : Bool) where
    constructor TName
    name : Name
    def  : TDef' n b

public export
SpecType : {n : Nat} -> {b : Bool} -> TDef' n b -> Type
SpecType _ {b = True} = Name
SpecType _ {b = False} {n} = Fin n

public export
SpecType' : Nat -> Bool -> Type
SpecType' _ True = Name
SpecType' n False = Fin n

||| TDef with variables
public export
TDef : Nat -> Type
TDef n = TDef' n True

||| TNamed with variables
public export
TNamed : Nat -> Type
TNamed n = TNamed' n True

||| Resolved TDef
public export
TDefR : Nat -> Type
TDefR n = TDef' n False

||| Resolved TNamed
public export 0
TNamedR : Nat -> Type
TNamedR n = TNamed' n False

public export
record TopLevelDef where
  constructor MkTopLevelDef
  specialized : List String
  typedefs : List1 (n ** TNamedR n)

||| Generate `[TVar 0, ..., TVar (n-1)]`.
public export
idVars : (n : Nat) -> Vect n (TDef' n b)
idVars Z = []
idVars (S n) = map TVar range

||| Apply a `TNamed` to the variable list `[TVar 0, ..., TVar (n-1)]`. Semantically, this is the same as
||| doing nothing, but it allows us to embed a named definition in a regular `TDef`.
public export
wrap : (n : Nat) -> TNamed' n b -> TDef' n b
wrap n tn = TApp tn (idVars n)

||| Alias one `TNamed` with a new name. Note: this is not the same as naming the underlying `TDef` again.
public export
alias : {n : Nat} -> Name -> TNamed' n b -> TNamed' n b
alias name tn = TName name (wrap n tn)

-- Surrounding character functions
export
parens : String -> String
parens "" = ""
parens s = "(" ++ s ++ ")"

export
parens' : String -> String
parens' s = if " " `isInfixOf` s then "(" ++ s ++ ")" else s

export
curly : String -> String
curly "" = ""
curly s = "{" ++ s ++ "}"

export
square : String -> String
square "" = ""
square s = "[" ++ s ++ "]"

||| Generate the canonical name of a closed type.
public export
makeName : TDef' 0 b -> Name
makeName  T0                     = "void"
makeName  T1                     = "unit"
makeName (TSum ts)               = "sum" ++ parens (concat . intersperse "," . map (assert_total makeName) $ ts)
makeName (TProd ts)              = "prod" ++ parens (concat . intersperse "," . map (assert_total makeName) $ ts)
makeName (TMu cases)             = concatMap fst cases
makeName (TApp f xs)             = name f ++ parens (concat . intersperse "," . map (assert_total makeName) $ xs)
makeName (RRef i)    {b = False} impossible
makeName (FRef i)    {b = True } = "ref"

-- Dealing with variables

public export
Ren : Nat -> Nat -> Type
Ren n m = Fin n -> Fin m

public export
ext : Ren n m -> Ren (S n) (S m)
ext s  FZ    = FZ
ext s (FS x) = FS (s x)

public export
rename : {m : Nat} -> Ren n m -> TDef' n b ->  TDef' m b
rename r          T0                     = T0
rename r          T1                     = T1
rename r         (TSum ts)               = assert_total $ TSum $ map (rename r) ts
rename r         (TProd ts)              = assert_total $ TProd $ map (rename r) ts
rename r         (TMu cs)                = assert_total $ TMu $ map (map $ rename (ext r)) cs
rename r         (TApp f xs)             = assert_total $ TApp f $ map (rename r) xs
rename r {m=Z}   (RRef i)    {b = False} = absurd $ r i
rename r {m=S m} (RRef i)    {b = False} = RRef $ r i
rename r {m=Z}   (TVar v)                = absurd $ r v
rename r {m=S m} (TVar v)                = TVar $ r v
rename r         (FRef i)    {b = True}  = FRef i

||| Add 1 to all de Bruijn-indices in a `TDef`.
||| Useful for including a predefined open definition into a `TMu` without touching the recursive variable.
public export
shiftVars : {n : Nat} -> TDef' n a -> TDef' (S n) a
shiftVars = rename FS

||| Get a list of the De Bruijn indices that are actually used in a `TDef`.
||| /!\ TDefR n will count resolved references as variables /!\
public export
getUsedIndices : TDef' n a -> List (Fin n)
getUsedIndices T0          = []
getUsedIndices T1          = []
getUsedIndices (TSum xs)   = assert_total $ List.nub $ concatMap getUsedIndices xs
getUsedIndices (TProd xs)  = assert_total $ List.nub $ concatMap getUsedIndices xs
getUsedIndices (TVar i)    = [i]
getUsedIndices (TMu xs)    = assert_total $ List.nub $ concatMap ((concatMap weedOutZero) . getUsedIndices . snd) xs
  where weedOutZero : Fin (S n) -> List (Fin n)
        weedOutZero FZ     = []
        weedOutZero (FS i) = [i]
getUsedIndices (TApp f xs) =
  let fUses = assert_total $ getUsedIndices (def f)
   in nub $ concatMap (assert_total getUsedIndices) $ map (flip index xs) fUses
getUsedIndices (RRef i)    {a = False} = [i]
getUsedIndices (FRef i)    {a = True } = []

||| Filter out the entries in an argument vector that are actually referred to by a `TDef`.
public export
getUsedVars : Vect n a -> (td : TDef' n b) -> Vect (List.length (getUsedIndices td)) a
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Substitute all variables in a `TDef` with a vector of arguments.
||| This also replaces resolved references
public export
ap : {m : Nat} -> TDef' n b -> Vect n (TDef' m b) -> TDef' m b
ap  T0         _                = T0
ap  T1         _                = T1
ap (TSum ts)   args             = assert_total $ TSum $ map (flip ap args) ts
ap (TProd ts)  args             = assert_total $ TProd $ map (flip ap args) ts
ap (TVar v)    args             = index v args
ap (TMu cs)    args             = assert_total $ TMu $ map (map (flip ap (TVar FZ :: map shiftVars args))) cs
ap (TApp f xs) args             = assert_total $ def f `ap` (map (flip ap args) xs)
ap (RRef i)    args {b = False} = Vect.index i args
ap (FRef i)    args {b = True } = FRef i

||| Substitute all variables in a `TNamed` with a vector of *closed* arguments.
public export
apN : TNamed' n a -> Vect n (TDef' 0 a) -> TNamed' 0 a
apN (TName name body) ts =
  let vars = getUsedVars ts body
      newName = parens (concat . intersperse "," . map makeName $ vars)
   in TName
        (name ++ newName)
        (body `ap` ts)

-------------------------------------------------------------------------------
-- Weakenings                                                                --
-------------------------------------------------------------------------------

public export
weakenLTE : Fin n -> LTE n m -> Fin m
weakenLTE  FZ     LTEZero impossible
weakenLTE (FS _)  LTEZero impossible
weakenLTE  FZ    (LTESucc y) = FZ
weakenLTE (FS x) (LTESucc y) = FS $ Typedefs.weakenLTE x y

mutual
  ||| Increase the type index representing the number of variables accessible
  ||| to a `TDef`, without actually changing the variables that are used by it.
  |||
  ||| @m The new amount of variables.
  public export
  weakenTDef : TDef' n a -> (m : Nat) -> LTE n m -> TDef' m a
  weakenTDef T0             _    _   = T0
  weakenTDef T1             _    _   = T1
  weakenTDef (TSum xs)      m    prf = TSum $ weakenTDefs xs m prf
  weakenTDef (TProd xs)     m    prf = TProd $ weakenTDefs xs m prf
  weakenTDef (TVar _)       Z    prf = absurd prf
  weakenTDef (TVar i)    (S m)   prf = TVar $ Fin.weakenLTE i prf
  weakenTDef (TMu xs)       m    prf = TMu $ weakenNTDefs xs (S m) (LTESucc prf)
  weakenTDef (TApp f xs)    m    prf = TApp f $ weakenTDefs xs m prf
  weakenTDef (RRef x)    (S m)   prf {a = False} = RRef $ Fin.weakenLTE x prf
  weakenTDef (FRef x)       m    prf {a = True } = FRef x

  public export
  weakenTDefs : Vect k (TDef' n a) -> (m : Nat) -> LTE n m -> Vect k (TDef' m a)
  weakenTDefs []      _ _   = []
  weakenTDefs (x::xs) m lte = weakenTDef x m lte :: weakenTDefs xs m lte

  public export
  weakenNTDefs : Vect k (Name, TDef' n a) -> (m : Nat) -> LTE n m -> Vect k (Name, TDef' m a)
  weakenNTDefs []          _ _   = []
  weakenNTDefs ((n,x)::xs) m lte = (n, weakenTDef x m lte) :: weakenNTDefs xs m lte

||| Increase the type index representing the number of variables accessible
||| to a `TNamed`, without actually changing the variables that are used by it.
|||
||| @m The new amount of variables.
public export
weakenTNamed : TNamed' n a -> (m : Nat) -> LTE n m -> TNamed' m a
weakenTNamed (TName n t) m prf = TName n (weakenTDef t m prf)

-------------------------------------------------------------------------------
-- Equality                                                                  --
-------------------------------------------------------------------------------

vectEq : Eq a => Vect n a -> Vect m a -> Bool
vectEq []      []      = True
vectEq (x::xs) (y::ys) = x == y && vectEq xs ys
vectEq _       _       = False

{-
mutual

  heteroEq : {n, m : Nat} -> TDef' n a -> TDef' m a -> Bool
  heteroEq {n} {m} tn tm with (cmp n m)
    heteroEq {n = n} {m = (plus _ (S y))} tn tm | (CmpLT y) = tm == (weakenTDef tn _ (lteAddRight n))
    heteroEq {n = m} {m = m} tn tm | CmpEQ = tn == (weakenTDef tm _ (lteAddRight m))
    heteroEq {n = (plus m (S x))} {m = m} tn tm | (CmpGT x) = tn == tm

  heteroEq {-n} {m-} tn tm with (cmp n m)
    heteroEq {-n} {m-} tn tm | (CmpLT y) = False --tm == (weakenTDef tn _ (lteAddRight n)) -- or should this be `False`?
    heteroEq {-n} {m-} tn tm | (CmpGT x) = False --tn == (weakenTDef tm _ (lteAddRight m)) -- or should this be `False`?
    heteroEq {-n} {m-} tn tm | (CmpEQ)   = False -- tn == tm

  heteroEqNamed : {n : Nat} -> {m : Nat} -> TNamed' n a -> TNamed' m a -> Bool
  heteroEqNamed (TName name t) (TName name' t') = name == name' && heteroEq t t'

  implementation Eq (TDef' n a) where
    (==) T0          T0            {a = a}     = True
    (==) T1          T1            {a = a}     = True
    (==) (TSum xs)   (TSum xs')    {a = a}     = assert_total $ vectEq xs xs'
    (==) (TProd xs)  (TProd xs')   {a = a}     = assert_total $ vectEq xs xs'
    (==) (TVar i)    (TVar i')     {a = a}     = i == i'
    (==) (TMu xs)    (TMu xs')     {a = a}     = assert_total $ vectEq xs xs'
    (==) (TApp f xs) (TApp f' xs') {a = a}     = assert_total $ heteroEqNamed f f' && vectEq xs xs'
    (==) (RRef n)    (RRef n')     {a = False} = n == n'
    (==) (FRef n)    (FRef n')     {a = False} impossible
    (==) (RRef n)    (RRef n')     {a = True}  impossible
    (==) (FRef n)    (FRef n')     {a = True}  = n == n'
    (==) _           _             {a = a} = False

implementation Eq (TNamed' n a) where
  (TName n t) == (TName n' t')       = n == n' && t == t'
  -}

-------------------------------------------------------------------------------
-- Meta                                                                      --
-------------------------------------------------------------------------------

pow : Nat -> TDef' n a -> TDef' n a
pow  Z        _ = T1
pow (S Z)     a = a
pow (S (S n)) a = TProd (a :: a :: replicate n a)

powN : (n : Nat) -> TNamed' n a -> TDef' n a
powN n tn = pow n (wrap n tn)

-- TODO add to stdlib?
minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     m    _   = rewrite minusZeroRight m in
                            plusZeroRightNeutral m
minusPlus (S _)  Z    lte = absurd lte
minusPlus (S n) (S m) lte = rewrite sym $ plusSuccRightSucc (m `minus` n) n in
                            ?huh --cong _ $ minusPlus n m (fromLteSucc lte)

-------------------------------------------------------------------------------
-- Printing                                                                  --
-------------------------------------------------------------------------------

mutual
  showTDef : TDef' n a -> String
  showTDef T0          = "0"
  showTDef T1          = "1"
  showTDef (TSum xs)   = parens $ showOp "+" xs
  showTDef (TProd xs)  = parens $ showOp "*" xs
  showTDef (TVar x)    = curly $ show $ finToNat x
  showTDef (TMu ms)    = parens $ "mu " ++ square (showNTDefs ms)
  showTDef (TApp f []) = name f
  showTDef (TApp f xs) = parens $ concat (intersperse " " (name f :: map (assert_total showTDef) xs))
  showTDef (FRef n)    {a = True} = n
  showTDef (RRef n)    {a = False} = curly $ show $ finToNat n

  showOp : String -> Vect k (TDef' n a) -> String
  showOp _  []         = ""
  showOp _  [x]        = showTDef x
  showOp op (x::y::ys) = showTDef x ++ " " ++ op ++ " " ++ assert_total (showOp op (y::ys))

  showNTDefs : Vect k (Name, TDef' n a) -> String
  showNTDefs []          = ""
  showNTDefs [(n,x)]     = n ++ ": " ++ assert_total (showTDef x)
  showNTDefs ((n,x)::xs) = n ++ ": " ++ assert_total (showTDef x) ++ ", " ++ assert_total (showNTDefs xs)

showTNamed : TNamed' n a -> String
showTNamed (TName n t) = parens $ n ++ " := " ++ showTDef t

Show (TDef' n a) where
  show = showTDef

Show (TNamed' n a) where
  show = showTNamed

-- Debug ----

-- we use a named implementation of `Show (Fin n)` to avoid possible conflicts
[finSimpleShow] Show (Fin k) where
  show = show . finToNat

mutual
  debugTDefVect : Vect k (TDef' n b) -> String
  debugTDefVect []        = "[]"
  debugTDefVect (x :: xs) = assert_total $
    square $ foldr (\elem, acc => acc ++ ", " ++ debugTDef elem) (debugTDef x) xs

  debugMu : Vect k (Name, TDef' (S n) b) -> String
  debugMu []        = "[]"
  debugMu (x :: xs) = assert_total $
    square $ foldr (\elem, acc => acc ++ ", " ++ debugNamedMu elem) (debugNamedMu x) xs
    where
      debugNamedMu : (Name, TDef' (S n) b) -> String
      debugNamedMu (name, tdef) = parens $ show name ++ ", " ++ debugTDef tdef

  ||| prints a faithful representation of the AST of a TDef
  debugTDef : TDef' n b -> String
  debugTDef T0          = "T0"
  debugTDef T1          = "T1"
  debugTDef (TSum  xs)  = "TSum " ++ debugTDefVect xs
  debugTDef (TProd xs)  = "TProd " ++ debugTDefVect xs
  debugTDef (TVar x)    = "TVar " ++ show @{finSimpleShow} x
  debugTDef (TMu ms)    = "TMu " ++ debugMu ms
  debugTDef (TApp f xs) = "TApp (" ++ debugTNamed f ++ ", " ++ debugTDefVect xs ++ ")"
  debugTDef (FRef n)    = "FRef " ++ show n
  debugTDef (RRef n)    = "RRef " ++ show @{finSimpleShow} n

  ||| prints a faithful representation of the AST of a TNamed
  debugTNamed : TNamed' n b -> String
  debugTNamed (TName name tdef) = "TName (" ++ show name ++ ", " ++ debugTDef tdef ++ ")"

{-
-}
