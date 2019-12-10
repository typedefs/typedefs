module Typedefs.Typedefs

import Data.Fin
import Data.Vect
import Data.NEList

import Typedefs.Names

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

    ||| A Reference to a named typedef
    TRef  : Name                                  -> TDef n

  ||| Named type definition.
  ||| @n The number of type variables in the type.
  record TNamed (n : Nat) where
    constructor TName
    name : Name
    def  : TDef n

record TopLevelDef where
  constructor MkTopLevelDef
  specialized : List String
  typedefs : NEList (n ** TNamed n)

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

parens' : String -> String
parens' s = if " " `isInfixOf` s then "(" ++ s ++ ")" else s

curly : String -> String
curly "" = ""
curly s = "{" ++ s ++ "}"

square : String -> String
square "" = ""
square s = "[" ++ s ++ "]"

||| Generate the canonical name of a closed type.
makeName : TDef 0 -> Name
makeName T0          = "void"
makeName T1          = "unit"
makeName (TSum ts)   = "sum" ++ parens (concat . intersperse "," . map (assert_total makeName) $ ts)
makeName (TProd ts)  = "prod" ++ parens (concat . intersperse "," . map (assert_total makeName) $ ts)
makeName (TMu cases) = concatMap fst cases
makeName (TApp f xs) = name f ++ parens (concat . intersperse "," . map (assert_total makeName) $ xs)
makeName (TRef n)    = n

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
shiftVars (TRef n)    = TRef n

||| Get a list of the De Bruijn indices that are actually used in a `TDef`.
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
getUsedIndices (TRef n)    = []

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
ap (TRef n)    _    = TRef n -- should we do `TRef $ n ++ (map (\t => " " ++ makeName t) args)` ?

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
  -- either use a proof that no TRefs exist or a proof that every
  -- TRef has a mapping to an Idris type
  Ty     tvars (TRef n)    = Void

-- Show and Eq instances

mutual

  showMu : (tvars : Vect n (a : Type ** a -> String)) -> (td : TDef (S n)) -> Mu (map DPair.fst tvars) td -> String
  showMu tvars td (Inn x) = "Inn " ++ parens' (showTy ((Mu (map DPair.fst tvars) td ** assert_total $ showMu tvars td)::tvars) td x)

  showTy : (tvars : Vect n (a : Type ** a -> String)) -> (td : TDef n) -> Ty (map DPair.fst tvars) td -> String
  showTy tvars T0                    x         impossible
  showTy tvars T1                    x         = show x
  showTy tvars (TSum [a,b])          (Left x)  = "Left " ++ parens' (showTy tvars a x)
  showTy tvars (TSum [a,b])          (Right x) = "Right " ++ parens' (showTy tvars b x)
  showTy tvars (TSum (a::b::c::xs))  (Left x)  = "Left " ++ parens' (showTy tvars a x)
  showTy tvars (TSum (a::b::c::xs))  (Right x) = "Right " ++ parens' (assert_total $ showTy tvars (TSum (b::c::xs))  x)
  showTy {n = n} tvars (TProd xs)    x         = parens (concat (List.intersperse ", " (showProd xs x)))
    where showProd : (ys : Vect (2 + k) (TDef n)) -> Tnary (map DPair.fst tvars) ys Pair -> List String
          showProd [a, b]        (x, y) = (showTy tvars a x)::[showTy tvars b y]
          showProd (a::b::c::ys) (x, y) = (showTy tvars a x)::showProd (b::c::ys) y
  showTy ((a ** showA)::tvars)     (TVar FZ)     x = showA x
  showTy {n = S (S n')} (_::tvars) (TVar (FS i)) x = showTy {n = S n'} tvars (TVar i) x
  showTy tvars                     (TMu m)       x = showMu tvars (args m) x
  showTy tvars                     (TApp f xs)   x = assert_total $ showTy tvars (def f `ap` xs) x
  showTy tvars                     (TRef n)      x = show n -- Is this correct?

Show (Mu [] td) where
  show y = showMu [] td y

mutual

  eqMu : (tvars : Vect n (a : Type ** a -> a -> Bool)) -> (td : TDef (S n)) ->
         Mu (map DPair.fst tvars) td -> Mu (map DPair.fst tvars) td  -> Bool
  eqMu tvars td (Inn x) (Inn x') = eqTy ((Mu (map DPair.fst tvars) td ** assert_total $ eqMu tvars td)::tvars) td x x'

  eqTy : (tvars : Vect n (a : Type ** a -> a -> Bool)) -> (td : TDef n) ->
         Ty (map DPair.fst tvars) td -> Ty (map DPair.fst tvars) td -> Bool
  eqTy tvars T0                    x x'        impossible
  eqTy tvars T1                    x x'      = x == x'
  eqTy tvars (TSum [a,b])          (Left x)  (Left x') = eqTy tvars a x x'
  eqTy tvars (TSum [a,b])          (Right x) (Right x') = eqTy tvars b x x'
  eqTy tvars (TSum (a::b::c::xs))  (Left x)  (Left x') = eqTy tvars a x x'
  eqTy tvars (TSum (a::b::c::xs))  (Right x) (Right x') = assert_total $ eqTy tvars (TSum (b::c::xs))  x x'
  eqTy {n = n} tvars (TProd xs)    x x' = eqProd xs x x'
    where eqProd : (ys : Vect (2 + k) (TDef n)) ->
                   Tnary (map DPair.fst tvars) ys Pair -> Tnary (map DPair.fst tvars) ys Pair -> Bool
          eqProd [a, b]        (x, y) (x', y') = (eqTy tvars a x x') && (eqTy tvars b y y')
          eqProd (a::b::c::ys) (x, y) (x', y') = (eqTy tvars a x x') && (eqProd (b::c::ys) y y')
  eqTy ((a ** eqA)::tvars)     (TVar FZ)       x x' = eqA x x'
  eqTy {n = S (S n')} (_::tvars) (TVar (FS i)) x x' = eqTy {n = S n'} tvars (TVar i) x x'
  eqTy tvars                     (TMu m)       x x' = eqMu tvars (args m) x x'
  eqTy tvars                     (TApp f xs)   x x' = assert_total $ eqTy tvars (def f `ap` xs) x x'
  eqTy tvars                     (TRef n)      x x' impossible
  eqTy tvars _ _ _ = False

Eq (Mu [] td) where
  y == y' = eqMu [] td y y'

------ meta ----------

pow : Nat -> TDef n -> TDef n
pow  Z        _ = T1
pow (S Z)     a = a
pow (S (S n)) a = TProd (a :: a :: replicate n a)

powN : Nat -> TNamed n -> TDef n
powN n tn = pow n (wrap tn)

-- TODO add to stdlib?
minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     m    _   = rewrite minusZeroRight m in
                            plusZeroRightNeutral m
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
  weakenTDef (TRef n)       _    _   = TRef n

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
  showTDef (TRef n)    = n

-- useful for debugging
--  showTDef (TApp f []) = name f ++ "<" ++ assert_total (showTDef (def f)) ++ ">"
--  showTDef (TApp f xs) = parens $ concat $ intersperse " " ((name f ++ "<" ++ assert_total (showTDef (def f)) ++ ">") :: map (assert_total showTDef) xs)

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

mutual

  heteroEq : {n : Nat} -> {m : Nat} -> TDef n -> TDef m -> Bool
  heteroEq {n} {m} tn tm with (cmp n m)
    heteroEq {n}     tn tm | (CmpLT y) = tm == (weakenTDef tn _ (lteAddRight n)) -- or should this be `False`?
    heteroEq     {m} tn tm | (CmpGT x) = tn == (weakenTDef tm _ (lteAddRight m)) -- or should this be `False`?
    heteroEq         tn tm | (CmpEQ)   = tn == tm

  heteroEqNamed : {n : Nat} -> {m : Nat} -> TNamed n -> TNamed m -> Bool
  heteroEqNamed (TName name t) (TName name' t') = name == name' && heteroEq t t'

  implementation Eq (TDef n) where
    T0            == T0              = True
    T1            == T1              = True
    (TSum xs)     == (TSum xs')      = assert_total $ vectEq xs xs'
    (TProd xs)    == (TProd xs')     = assert_total $ vectEq xs xs'
    (TVar i)      == (TVar i')       = i == i'
    (TMu xs)      == (TMu xs')       = assert_total $ vectEq xs xs'
    (TApp f xs)   == (TApp f' xs')   = assert_total $ heteroEqNamed f f' && vectEq xs xs'
    (TRef n)      == (TRef n')       = n == n'
    _             == _               = False

implementation Eq (TNamed n) where
  (TName n t) == (TName n' t')       = n == n' && t == t'

-- Debug ----

-- we use a named implementation of `Show (Fin n)` to avoid possible conflicts
[finSimpleShow] Show (Fin k) where
  show = show . finToNat

mutual
  debugTDefVect : Vect k (TDef n) -> String
  debugTDefVect []        = "[]"
  debugTDefVect (x :: xs) = assert_total $
    square $ foldr (\elem, acc => acc ++ ", " ++ debugTDef elem) (debugTDef x) xs

  debugMu : Vect k (Name, TDef (S n)) -> String
  debugMu []        = "[]"
  debugMu (x :: xs) = assert_total $
    square $ foldr (\elem, acc => acc ++ ", " ++ debugNamedMu elem) (debugNamedMu x) xs
    where
      debugNamedMu : (Name, TDef (S n)) -> String
      debugNamedMu (name, tdef) = parens $ show name ++ ", " ++ debugTDef tdef

  ||| prints a faithful representation of the AST of a TDef
  debugTDef : TDef n -> String
  debugTDef T0          = "T0"
  debugTDef T1          = "T1"
  debugTDef (TSum  xs)  = "TSum " ++ debugTDefVect xs
  debugTDef (TProd xs)  = "TProd " ++ debugTDefVect xs
  debugTDef (TVar x)    = "TVar " ++ show @{finSimpleShow} x
  debugTDef (TMu ms)    = "TMu " ++ debugMu ms
  debugTDef (TApp f xs) = "TApp (" ++ debugTNamed f ++ ", " ++ debugTDefVect xs ++ ")"
  debugTDef (TRef n)    = "TRef " ++ show n

  ||| prints a faithful representation of the AST of a TNamed
  debugTNamed : TNamed n -> String
  debugTNamed (TName name tdef) = "TName (" ++ show name ++ ", " ++ debugTDef tdef ++ ")"
