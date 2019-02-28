module Typedefs

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Names

%default total
%access public export

mutual
  ||| Type definition
  ||| @n The number of type variables in the type
  data TDef : (n:Nat) -> Type where
    ||| The empty type
    T0    :                                          TDef n

    ||| The unit type
    T1    :                                          TDef n

    ||| The coproduct type
    TSum  :             Vect (2 + k) (TDef n)     -> TDef n

    ||| The product type
    TProd :             Vect (2 + k) (TDef n)     -> TDef n

    ||| A type variable
    ||| @i De Bruijn index
    TVar  :             (i:Fin (S n))             -> TDef (S n)

    ||| Mu
    TMu   :             Vect k (Name, TDef (S n)) -> TDef n

    ||| Application of a named type to a vector of arguments.
    TApp  : TNamed k -> Vect k (TDef n)           -> TDef n

  ||| Named type definition.
  ||| @n The number of type variables in the type.
  data TNamed : (n : Nat) -> Type where
    TName : Name -> TDef n -> TNamed n

||| Proof that all variable indices in a `TDef` are less than the `bound`.
data VarsLT : (bound : Nat) -> TDef n -> Type where
  T0Max    :                                                       VarsLT bound T0
  T1Max    :                                                       VarsLT bound T1
  TSumMax  : All (VarsLT bound) ts                              -> VarsLT bound (TSum ts)
  TProdMax : All (VarsLT bound) ts                              -> VarsLT bound (TProd ts)
  TVarMax  : LT (finToNat i) bound                              -> VarsLT bound (TVar i)
  TMuMax   : All (VarsLT (S bound)) (map Prelude.Basics.snd cs) -> VarsLT bound (TMu cs)
  TAppMax  : All (VarsLT bound) xs                              -> VarsLT bound (TApp f xs)

mutual
  ||| Weaken the upper bound of a `VarsLT` proof.
  weakenVarsLT : LTE n m -> VarsLT n td -> VarsLT m td
  weakenVarsLT _ T0Max           = T0Max
  weakenVarsLT _ T1Max           = T1Max
  weakenVarsLT p (TSumMax prfs)  = TSumMax  (weakenVarsLTs p           prfs)
  weakenVarsLT p (TProdMax prfs) = TProdMax (weakenVarsLTs p           prfs)
  weakenVarsLT p (TVarMax prf)   = TVarMax  (lteTransitive prf         p)
  weakenVarsLT p (TMuMax prfs)   = TMuMax   (weakenVarsLTs (LTESucc p) prfs)
  weakenVarsLT p (TAppMax prfs)  = TAppMax  (weakenVarsLTs p           prfs)

  ||| Weaken the upper bound of a list of `VarsLT` proof.
  weakenVarsLTs : LTE n m -> All (VarsLT n) ts -> All (VarsLT m) ts
  weakenVarsLTs _ Nil         = Nil
  weakenVarsLTs p (prf::prfs) = weakenVarsLT p prf :: weakenVarsLTs p prfs

mutual
  ||| Generate a `VarsLT` proof with a tight bound.
  tightMaxVar : (td : TDef n) -> (m ** VarsLT m td)
  tightMaxVar T0          = (0 ** T0Max)
  tightMaxVar T1          = (0 ** T1Max)
  tightMaxVar (TSum ts)   = let maxes = tightMaxVars ts 
                             in (fst maxes ** TSumMax (snd maxes))
  tightMaxVar (TProd ts)  = let maxes = tightMaxVars ts 
                             in (fst maxes ** TProdMax (snd maxes))
  tightMaxVar (TVar i)    = (S (finToNat i) ** TVarMax lteRefl)
  tightMaxVar (TMu cs)    = ?tightTMuVars
  tightMaxVar (TApp f xs) = let maxes = tightMaxVars xs
                             in (fst maxes ** TAppMax (snd maxes))

  ||| Generate a list of `VarsLT` proofs, with the bound as tight as the loosest element of the input. 
  tightMaxVars : (ts : Vect k (TDef n)) -> (m ** All (VarsLT m) ts)
  tightMaxVars [] = (0 ** Nil)
  tightMaxVars (t::ts) = let (tMax ** tPrf) = tightMaxVar t
                             (tsMax ** tsPrfs) = tightMaxVars ts
                          in case cmp tMax tsMax of
                              CmpLT y => (tMax + S y ** (weakenVarsLT (lteAddRight tMax) tPrf :: tsPrfs))
                              CmpEQ   => (tMax ** (tPrf :: tsPrfs))
                              CmpGT x => (tsMax + S x ** (tPrf :: weakenVarsLTs (lteAddRight tsMax) tsPrfs))

||| A `Nat` can always be turned into a `Fin` if it is less than the bound.
natToFinTotal : {n : Nat} -> LT n m -> Fin m
natToFinTotal {n=Z}   (LTESucc _) = FZ
natToFinTotal {n=S n} (LTESucc p) = FS (natToFinTotal {n} p)

mutual
  ||| Given a proof that the number of free variables in `td` is less than the `bound`,
  ||| re-index this `TDef` using `bound`. 
  tightenTDef : VarsLT bound td -> TDef bound
  tightenTDef               T0Max           = T0
  tightenTDef               T1Max           = T1
  tightenTDef               (TSumMax prfs)  = TSum   (tightenTDefs  prfs)
  tightenTDef               (TProdMax prfs) = TProd  (tightenTDefs  prfs)
  tightenTDef {bound=S _}   (TVarMax prf)   = TVar   (natToFinTotal prf)
  tightenTDef               (TMuMax prfs)   = TMu    (tightenNTDefs prfs)
  tightenTDef {td=TApp f _} (TAppMax prfs)  = TApp f (tightenTDefs  prfs)

  ||| Given proofs that the number of free variables in the elements of `ts` is less than the `bound`,
  ||| re-index these `TDef`s using `bound`.
  tightenTDefs : {ts : Vect k (TDef n)} -> All (VarsLT bound) ts -> Vect k (TDef bound)
  tightenTDefs Nil = []
  tightenTDefs (prf::prfs) = tightenTDef prf :: tightenTDefs prfs

  tightenNTDefs : {cs : Vect k (Name, TDef n)} -> All (VarsLT bound) (map Prelude.Basics.snd cs) -> Vect k (Name, TDef bound)
  tightenNTDefs {cs=[]}       Nil         = []
  tightenNTDefs {cs=(n,_)::_} (prf::prfs) = (n,tightenTDef prf) :: tightenNTDefs prfs 

||| Decision procedure for determining whether all variable indices in a `TDef`
||| are strictly less than some bound.
decMaxVar : (bound : Nat) -> (td : TDef n) -> Dec (VarsLT bound td)
decMaxVar _     T0          = Yes T0Max
decMaxVar _     T1          = Yes T1Max
decMaxVar bound (TSum ts)   = case all (decMaxVar bound) ts of
                                Yes prfs   => Yes    (TSumMax prfs)
                                No  contra => No  $ \(TSumMax prfs)  => contra prfs
decMaxVar bound (TProd ts)  = case all (decMaxVar bound) ts of
                                Yes prfs   => Yes    (TProdMax prfs)
                                No  contra => No  $ \(TProdMax prfs) => contra prfs
decMaxVar bound (TVar i)    = case isLTE (S (finToNat i)) bound of
                                Yes prf    => Yes    (TVarMax prf)
                                No  contra => No  $ \(TVarMax prf)   => contra prf
decMaxVar bound (TMu cases) = case all (decMaxVar (S bound)) (map snd cases) of
                                Yes prfs   => Yes    (TMuMax prfs)
                                No  contra => No  $ \(TMuMax prfs)   => contra prfs
decMaxVar bound (TApp _ xs) = case all (decMaxVar bound) xs of
                                Yes prfs   => Yes    (TAppMax prfs)
                                No  contra => No  $ \(TAppMax prfs)  => contra prfs

||| Proof that a `TDef` does not contain any free variables.
NoFreeVars : TDef n -> Type
NoFreeVars = VarsLT 0

||| Get the name of a `TNamed`.
name : TNamed n -> Name
name (TName n _) = n

||| Get the `TDef` that is named by a `TNamed`.
def : TNamed n -> TDef n
def (TName _ t) = t

||| Generate `[TVar 0, ..., TVar (n-1)]`.
idVars : Vect n (TDef n)
idVars {n=Z}   = []
idVars {n=S _} = map TVar range

||| Apply a `TNamed` to the variable list `[TVar 0, ..., TVar (n-1)]`. Semantically, this is the same as
||| doing nothing, but it allows us to embed a named definition in a regular `TDef`.
wrap : TNamed n -> TDef n
wrap tn = TApp tn idVars

||| Alias one `TNamed` with a new name. Note: this is not the same as naming the underlying `TDef` again.
alias : Name -> TNamed n -> TNamed n
alias name tn = TName name (wrap tn)

parens : String -> String
parens "" = ""
parens s = "(" ++ s ++ ")"

curly : String -> String
curly "" = ""
curly s = "{" ++ s ++ "}"

square : String -> String
square "" = ""
square s = "[" ++ s ++ "]"

||| Generate the canonical name of a closed type.
makeName : TDef 0 -> Name
makeName T0          = "emptyType"
makeName T1          = "singletonType"
makeName (TSum ts)   = "sum" ++ parens (concat . intersperse "," . map (assert_total makeName) $ ts)
makeName (TProd ts)  = "prod" ++ parens (concat . intersperse "," . map (assert_total makeName) $ ts)
makeName (TMu cases) = concatMap fst cases
makeName (TApp f xs) = name f ++ parens (concat . intersperse "," . map (assert_total makeName) $ xs)

||| Add 1 to all de Bruijn-indices in a `TDef`.
||| Useful for including a predefined open definition into a `TMu` without touching the recursive variable.
shiftVars : TDef n -> TDef (S n)
shiftVars T0          = T0
shiftVars T1          = T1
shiftVars (TSum ts)   = assert_total $ TSum $ map shiftVars ts
shiftVars (TProd ts)  = assert_total $ TProd $ map shiftVars ts
shiftVars (TVar v)    = TVar $ shift 1 v
shiftVars (TMu cs)    = assert_total $ TMu $ map (map shiftVars) cs
shiftVars (TApp f xs) = assert_total $ TApp f $ map shiftVars xs 

||| Get a list of the de Brujin indices that are actually used in a `TDef`.
getUsedIndices : TDef n -> List (Fin n)
getUsedIndices T0          = []
getUsedIndices T1          = []
getUsedIndices (TSum xs)   = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TProd xs)  = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TVar i)    = [i]
getUsedIndices (TMu xs)    = assert_total $ nub $ concatMap ((concatMap weedOutZero) . getUsedIndices . snd) xs
  where weedOutZero : Fin (S n) -> List (Fin n)
        weedOutZero FZ     = []
        weedOutZero (FS i) = [i]
getUsedIndices (TApp f xs) = let fUses = assert_total $ getUsedIndices (def f)
                              in nub $ concatMap (assert_total getUsedIndices) $ map (flip index xs) fUses

||| Filter out the entries in an argument vector that are actually referred to by a `TDef`.
getUsedVars : Vect n a -> (td: TDef n) -> Vect (length (getUsedIndices td)) a
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Substitute all variables in a `TDef` with a vector of arguments.
ap : TDef n -> Vect n (TDef m) -> TDef m
ap T0          _    = T0
ap T1          _    = T1
ap (TSum ts)   args = assert_total $ TSum $ map (flip ap args) ts
ap (TProd ts)  args = assert_total $ TProd $ map (flip ap args) ts
ap (TVar v)    args = index v args
ap (TMu cs)    args = assert_total $ TMu $ map (map (flip ap (TVar 0 :: map shiftVars args))) cs
ap (TApp f xs) args = assert_total $ def f `ap` (map (flip ap args) xs)

||| Substitute all variables in a `TNamed` with a vector of *closed* arguments.
apN : TNamed n -> Vect n (TDef 0) -> TNamed 0
apN (TName n body) ts = TName
                            (n ++ parens (concat . intersperse "," . map makeName $ getUsedVars ts body))
                            (body `ap` ts)

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
  Ty     tvars (TApp f xs) = assert_total $ Ty tvars $ def f `ap` xs -- TODO: could be done properly

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
  weakenTDef (TApp f xs)    m    prf = TApp f $ weakenTDefs xs m prf

  weakenTDefs : Vect k (TDef n) -> (m : Nat) -> LTE n m -> Vect k (TDef m)
  weakenTDefs []      _ _   = []
  weakenTDefs (x::xs) m lte = weakenTDef x m lte :: weakenTDefs xs m lte

  weakenNTDefs : Vect k (Name, TDef n) -> (m : Nat) -> LTE n m -> Vect k (Name, TDef m)
  weakenNTDefs []          _ _   = []
  weakenNTDefs ((n,x)::xs) m lte = (n, weakenTDef x m lte) :: weakenNTDefs xs m lte

||| Increase the type index representing the number of variables accessible
||| to a `TNamed`, without actually changing the variables that are used by it.
|||
||| @m The new amount of variables.
weakenTNamed : TNamed n -> (m : Nat) -> LTE n m -> TNamed m
weakenTNamed (TName n t) m prf = TName n (weakenTDef t m prf)

-------- printing -------

mutual
  showTDef : TDef n -> String
  showTDef T0          = "0"
  showTDef T1          = "1"
  showTDef (TSum xs)   = parens $ showOp "+" xs
  showTDef (TProd xs)  = parens $ showOp "*" xs
  showTDef (TVar x)    = curly $ show $ toNat x
  showTDef (TMu ms)    = parens $ "mu " ++ square (showNTDefs ms)
  showTDef (TApp f []) = name f
  showTDef (TApp f xs) = parens $ concat (intersperse " " (name f :: map (assert_total showTDef) xs)) 

  showOp : String -> Vect k (TDef n) -> String
  showOp _  []         = ""
  showOp _  [x]        = showTDef x
  showOp op (x::y::ys) = showTDef x ++ " " ++ op ++ " " ++ showOp op (y::ys)

  showNTDefs : Vect k (Name, TDef n) -> String
  showNTDefs []          = ""
  showNTDefs [(n,x)]     = n ++ ": " ++ showTDef x
  showNTDefs ((n,x)::xs) = n ++ ": " ++ showTDef x ++ ", " ++ showNTDefs xs

showTNamed : TNamed n -> String
showTNamed (TName n t) = parens $ n ++ " := " ++ showTDef t

Show (TDef n) where
  show = showTDef

Show (TNamed n) where
  show = showTNamed

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
  (TApp f xs)   == (TApp f' xs')   = assert_total $ name f == name f' && heteroEq (def f) (def f') && vectEq xs xs'
    where
    heteroEq : {n : Nat} -> {m : Nat} -> TDef n -> TDef m -> Bool
    heteroEq {n} {m} tn tm with (cmp n m)
      heteroEq {n}     tn tm | (CmpLT y) = assert_total $ tm == (weakenTDef tn _ (lteAddRight n)) -- or should this be `False`?
      heteroEq     {m} tn tm | (CmpGT x) = assert_total $ tn == (weakenTDef tm _ (lteAddRight m)) -- or should this be `False`?
      heteroEq         tn tm | (CmpEQ)   = assert_total $ tn == tm
  _             == _               = False
