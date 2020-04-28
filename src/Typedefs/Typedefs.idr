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
  ||| @b A flag to indicate whether the TDef contains unknown references
  data TDef' : (n : Nat) -> (b : Bool) -> Type where
    ||| The empty type
    T0    :                                                TDef' n b

    ||| The unit type
    T1    :                                                TDef' n b

    ||| The coproduct type
    TSum  :                Vect (2 + k) (TDef' n b)     -> TDef' n b

    ||| The product type
    TProd :                Vect (2 + k) (TDef' n b)     -> TDef' n b

    ||| A type variable
    ||| @i De Bruijn index
    TVar  :                (i:Fin (S n))                -> TDef' (S n) b

    ||| Mu
    TMu   :                Vect k (Name, TDef' (S n) b) -> TDef' n b

    ||| Application of a named type to a vector of arguments.
    TApp  : TNamed' k b -> Vect k (TDef' n b)           -> TDef' n b

    ||| A resolved reference to an unknown typedef
    RRef  : Fin (S n)                                   -> TDef' (S n) False

    ||| A free reference to an unknown typedef
    FRef  : Name                                        -> TDef' n True

  ||| Named type definition.
  ||| @n The number of type variables in the type.
  record TNamed' (n : Nat) (b : Bool) where
    constructor TName
    name : Name
    def  : TDef' n b

SpecType : TDef' n b -> Type
SpecType _ {b = True} = Name
SpecType _ {b = False} {n} = Fin n

SpecType' : Nat -> Bool -> Type
SpecType' _ True = Name
SpecType' n False = Fin n

||| TDef with variables
TDef : Nat -> Type
TDef n = TDef' n True

||| TNamed with variables
TNamed : Nat -> Type
TNamed n = TNamed' n True

||| Resolved TDef
TDefR : Nat -> Type
TDefR n = TDef' n False

||| Resolved TNamed
TNamedR : Nat -> Type
TNamedR n = TNamed' n False

record TopLevelDef where
  constructor MkTopLevelDef
  specialized : List String
  typedefs : NEList (n ** TNamedR n)

||| Generate `[TVar 0, ..., TVar (n-1)]`.
idVars : Vect n (TDef' n b)
idVars {n=Z}   = []
idVars {n=S _} = map TVar range

||| Apply a `TNamed` to the variable list `[TVar 0, ..., TVar (n-1)]`. Semantically, this is the same as
||| doing nothing, but it allows us to embed a named definition in a regular `TDef`.
wrap : TNamed' n b -> TDef' n b
wrap tn = TApp tn idVars

||| Alias one `TNamed` with a new name. Note: this is not the same as naming the underlying `TDef` again.
alias : Name -> TNamed' n b -> TNamed' n b
alias name tn = TName name (wrap tn)

-- Surrounding character functions
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

Ren : Nat -> Nat -> Type
Ren n m = Fin n -> Fin m

ext : Ren n m -> Ren (S n) (S m)
ext s  FZ    = FZ
ext s (FS x) = FS (s x)

rename : Ren n m -> TDef' n b ->  TDef' m b
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
shiftVars : TDef' n a -> TDef' (S n) a
shiftVars = rename FS

||| Get a list of the De Bruijn indices that are actually used in a `TDef`.
||| /!\ TDefR n will count resolved references as variables /!\
getUsedIndices : TDef' n a -> List (Fin n)
getUsedIndices T0          = []
getUsedIndices T1          = []
getUsedIndices (TSum xs)   = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TProd xs)  = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TVar i)    = [i]
getUsedIndices (TMu xs)    = assert_total $ nub $ concatMap ((concatMap weedOutZero) . getUsedIndices . snd) xs
  where weedOutZero : Fin (S n) -> List (Fin n)
        weedOutZero FZ     = []
        weedOutZero (FS i) = [i]
getUsedIndices (TApp f xs) =
  let fUses = assert_total $ getUsedIndices (def f)
   in nub $ concatMap (assert_total getUsedIndices) $ map (flip index xs) fUses
getUsedIndices (RRef i)    {a = False} = [i]
getUsedIndices (FRef i)    {a = True } = []

||| Filter out the entries in an argument vector that are actually referred to by a `TDef`.
getUsedVars : Vect n a -> (td : TDef' n b) -> Vect (List.length (getUsedIndices td)) a
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Substitute all variables in a `TDef` with a vector of arguments.
||| This also replaces resolved references
ap : TDef' n b -> Vect n (TDef' m b) -> TDef' m b
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
apN : TNamed' n a -> Vect n (TDef' 0 a) -> TNamed' 0 a
apN (TName name body) ts =
  let vars = getUsedVars ts body
      newName = parens (concat . intersperse "," . map makeName $ vars)
   in TName
        (name ++ newName)
        (body `ap` ts)

mutual
  data Mu : Vect n Type -> TDef' (S n) a -> Type where
    Inn : Ty (Mu tvars m :: tvars) m -> Mu tvars m

  args : Vect k (String, TDef' (S n) a) -> TDef' (S n) a
  args []                 = T0
  args [(_,m)]            = m
  args ((_,m)::(_,l)::ms) = TSum (m :: l :: map snd ms)

  Tnary : Vect n Type -> Vect (2 + k) (TDefR n) -> (Type -> Type -> Type) -> Type
  Tnary tvars [x, y]              c = c (Ty tvars x) (Ty tvars y)
  Tnary tvars (x :: y :: z :: zs) c = c (Ty tvars x) (Tnary tvars (y :: z :: zs) c)

  ||| Interpret a type definition as an Idris `Type`. In `tvars : Vect n`, we
  ||| need to provide an Idris type for each of the `n` type variables in the
  ||| typedef. The De Bruijn indices in the `TVar`s in this typedef will be
  ||| mapped onto (i.e. instantiated at) the Idris types in `tvars`.
  Ty : Vect n Type -> TDefR n -> Type
  Ty     tvars T0                      = Void
  Ty     tvars T1                      = Unit
  Ty {n} tvars (TSum xs)               = Tnary tvars xs Either
  Ty {n} tvars (TProd xs)              = Tnary tvars xs Pair
  Ty     tvars (TVar v)                = Vect.index v tvars
  Ty     tvars (TMu m)                 = Mu tvars (args m)
  Ty     tvars (TApp (TName n def) xs) =
    assert_total $ Ty tvars $ def `ap` xs -- TODO: could be done properly
  Ty     tvars (RRef i)                = Vect.index i tvars

TypeConstructor : Nat -> Type
TypeConstructor Z = Type
TypeConstructor (S n) = Type -> TypeConstructor n

ApplyVect : Vect n Type -> TypeConstructor n -> Type
ApplyVect [] c = c
ApplyVect (x :: xs) c {n = S k} = ApplyVect xs (c x)

ReverseVect : (mkType : Vect n Type -> Type) -> TypeConstructor n
ReverseVect mkType {n = Z} = mkType []
ReverseVect mkType {n = (S k)} = \arg => ReverseVect (popHead mkType arg)
  where
    popHead : (Vect (S n) Type -> Type) -> Type -> Vect n Type -> Type
    popHead f t ts = f (t :: ts)

||| Converts a typedefs of `n` free variables into a type constructor that expects n arguments
AlphaTy : TDefR n -> TypeConstructor n
AlphaTy tdef = ReverseVect (flip Ty tdef)

NatSum : {f : Nat -> Type} -> Vect n (k : Nat ** f k) -> Nat
NatSum [] = Z
NatSum ((x ** _) :: xs) = x + NatSum xs

constructTypes : (types : Vect n (k ** TypeConstructor k)) -> Vect (NatSum types) Type -> Vect n Type
constructTypes [] [] = []
constructTypes ((k ** tc) :: xs) args = let
  (pre, post) = splitAt k args
  in ApplyVect pre tc :: constructTypes xs post

||| Given a vector of type constructors and a TDef construct the Idris type
||| from it using the second vector to instanciate the constructors
BetaTy : (types : Vect n (k ** TypeConstructor k)) -> TDefR n
     -> Vect (NatSum types) Type -> Type
BetaTy types tdef args = Ty (constructTypes types args) tdef

||| Given a list of type constructors fill the holes with them and return a new type constructor
GammaTy : (types : Vect n (k ** TypeConstructor k)) -> TDefR n
     -> TypeConstructor (NatSum types)
GammaTy types tdef = ReverseVect {n=NatSum types} (BetaTy types tdef)

||| Since `convertTy` is an identity function it is safe to assume this one is too
convertTy' : Ty ts (TApp f ys) -> Ty ts (ap (def f) ys)
convertTy' x = believe_me x

-- `showTy` just needs a little nudge in the right direction
%inline
convertTy : {n : Name} -> Ty v (TApp (TName n def) xs) -> Ty v (def `ap` xs)
convertTy x {def = T0       } = x
convertTy x {def = T1       } = x
convertTy x {def = TSum xs  } = x
convertTy x {def = TProd xs } = x
convertTy x {def = TVar i   } = x
convertTy x {def = TMu xs   } = x
convertTy x {def = TApp y xs} = x
convertTy x {def = RRef y   } = x

convertPrf : Ty v (ap def xs) = Ty v (TApp (TName n def) xs)
convertPrf {def = T0} = Refl
convertPrf {def = T1} = Refl
convertPrf {def = (TSum xs)} = Refl
convertPrf {def = (TProd xs)} = Refl
convertPrf {def = (TVar i)} = Refl
convertPrf {def = (TMu xs)} = Refl
convertPrf {def = (TApp x xs)} = Refl
convertPrf {def = (RRef x)} = Refl

-- TODO we should either finish mu/app cases or save some space by
-- making both of these into `really_believe_me` one-liners.
-- This is safe because adding/removing an unused var is a no-op.
ignoreShift : {t : TDefR n} -> Ty (var::vars) (shiftVars t) -> Ty vars t
ignoreShift {t=T0}                     ty         = absurd ty
ignoreShift {t=T1}                     ()         = ()
ignoreShift {t=TSum [x,y]}             (Left ty)  = Left $ ignoreShift ty
ignoreShift {t=TSum [x,y]}             (Right ty) = Right $ ignoreShift ty
ignoreShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ ignoreShift ty
ignoreShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ ignoreShift {t=TSum (y::z::ts)} ty
ignoreShift {t=TProd [x,y]}            (ty1,ty2)  = (ignoreShift ty1,ignoreShift ty2)
ignoreShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (ignoreShift ty1,ignoreShift {t=TProd (y::z::ts)} ty2)
ignoreShift {t=TMu cs}                 (Inn ty)   = Inn $ really_believe_me ty
ignoreShift {t=TApp (TName nam df) xs}  ty        = really_believe_me ty
ignoreShift {t=TVar v}                  ty        = ty
ignoreShift {t=RRef i}                  ty        = ty

addShift : {t : TDefR n} -> Ty vars t -> Ty (var::vars) (shiftVars t)
addShift {t=T0}                     ty         = absurd ty
addShift {t=T1}                     ()         = ()
addShift {t=TSum [x,y]}             (Left ty)  = Left $ addShift ty
addShift {t=TSum [x,y]}             (Right ty) = Right $ addShift ty
addShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ addShift ty
addShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ addShift {t=TSum (y::z::ts)} ty
addShift {t=TProd [x,y]}            (ty1,ty2)  = (addShift ty1,addShift ty2)
addShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (addShift ty1,addShift {t=TProd (y::z::ts)} ty2)
addShift {t=TMu cs}                 (Inn ty)   = Inn $ really_believe_me ty
addShift {t=TApp (TName nam df) xs}  ty        = really_believe_me ty
addShift {t=TVar v}                  ty        = ty
addShift {t=RRef i}                  ty        = ty

-- Show and Eq instances

mutual

  showMu : (tvars : Vect n (a : Type ** a -> String)) -> (td : TDef' (S n) b) -> Mu (map DPair.fst tvars) td -> String
  showMu tvars td (Inn x) = "Inn " ++ parens' (showTy ((Mu (map DPair.fst tvars) td ** assert_total $ showMu tvars td)::tvars) td x)

  ||| Print the content of a TDef provided functions to display Types as strings
  ||| @tvars a vector of n functions that map types to their string representation
  ||| @td the tdef to show
  ||| @x the idris type represented by `td` using `tvars` for free variables
  showTy : (tvars : Vect n (a : Type ** a -> String))
        -> (td : TDefR n)
        -> (x : Ty (map DPair.fst tvars) td)
        -> String
  showTy                  tvars  T0                          x        impossible
  showTy                  tvars  T1                          x        = show x
  showTy                  tvars  (TSum [a,b])               (Left x)  = "Left " ++ parens' (showTy tvars a x)
  showTy                  tvars  (TSum [a,b])               (Right x) = "Right " ++ parens' (showTy tvars b x)
  showTy                  tvars  (TSum (a::b::c::xs))       (Left x)  = "Left " ++ parens' (showTy tvars a x)
  showTy                  tvars  (TSum (a::b::c::xs))       (Right x) = "Right " ++ parens' (assert_total $ showTy tvars (TSum (b::c::xs)) x)
  showTy   ((a ** showA)::tvars) (TVar FZ)                   x        = showA x
  showTy {n=S (S n')} (_::tvars) (TVar (FS i))               x        = showTy {n = S n'} tvars (TVar i) x
  showTy                  tvars  (TMu m)                     x        = showMu tvars (args m) x
  showTy   ((a ** showA)::tvars) (RRef FZ)                   x        = showA x
  showTy {n=S (S n')} (_::tvars) (RRef (FS i))               x        = showTy {n = S n'} tvars (RRef i) x
  showTy                  tvars  (TApp (TName name def) xs)  x        = assert_total $ showTy tvars (def `ap` xs) (convertTy x)
  showTy {n}              tvars  (TProd xs)                  x        = parens $ concat $ List.intersperse ", " (showProd xs x)
    where showProd : (ys : Vect (2 + k) (TDefR n)) -> Tnary (map DPair.fst tvars) ys Pair -> List String
          showProd [a, b]        (x, y) = (showTy tvars a x)::[showTy tvars b y]
          showProd (a::b::c::ys) (x, y) = (showTy tvars a x)::showProd (b::c::ys) y

Show (Mu [] td) where
  show y = showMu [] td y

mutual

  eqMu : (tvars : Vect n (a : Type ** a -> a -> Bool)) -> (td : TDefR (S n)) ->
         Mu (map DPair.fst tvars) td -> Mu (map DPair.fst tvars) td  -> Bool
  eqMu tvars td (Inn x) (Inn x') = eqTy ((Mu (map DPair.fst tvars) td ** assert_total $ eqMu tvars td)::tvars) td x x'

  eqTy : (tvars : Vect n (a : Type ** a -> a -> Bool)) -> (td : TDefR n) ->
         Ty (map DPair.fst tvars) td -> Ty (map DPair.fst tvars) td -> Bool
  eqTy tvars T0                    x x'        impossible
  eqTy tvars T1                    x x'      = x == x'
  eqTy tvars (TSum [a,b])          (Left x)  (Left x') = eqTy tvars a x x'
  eqTy tvars (TSum [a,b])          (Right x) (Right x') = eqTy tvars b x x'
  eqTy tvars (TSum (a::b::c::xs))  (Left x)  (Left x') = eqTy tvars a x x'
  eqTy tvars (TSum (a::b::c::xs))  (Right x) (Right x') = assert_total $ eqTy tvars (TSum (b::c::xs))  x x'
  eqTy {n = n} tvars (TProd xs)    x x' = eqProd xs x x'
    where eqProd : (ys : Vect (2 + k) (TDefR n))
                -> Tnary (map DPair.fst tvars) ys Pair
                -> Tnary (map DPair.fst tvars) ys Pair -> Bool
          eqProd [a, b]        (x, y) (x', y') = (eqTy tvars a x x') && (eqTy tvars b y y')
          eqProd (a::b::c::ys) (x, y) (x', y') = (eqTy tvars a x x') && (eqProd (b::c::ys) y y')
  eqTy ((a ** eqA)::tvars)     (TVar FZ)         x x' = eqA x x'
  eqTy {n = S (S n')} (_::tvars) (TVar (FS i))   x x' = eqTy {n = S n'} tvars (TVar i) x x'
  eqTy tvars                     (TMu m)         x x' = eqMu tvars (args m) x x'
  eqTy tvars      (TApp (TName name def) xs)     x x' = assert_total $ eqTy tvars (def `ap` xs) (convertTy x) (convertTy x')
  eqTy ((a ** eqA)::tvars)       (RRef FZ)       x x' = eqA x x'
  eqTy {n = S (S n')} (_::tvars) (RRef (FS i))   x x' = eqTy {n = S n'} tvars (RRef i) x x'
  eqTy tvars _ _ _ = False

||| Equality instance for Mu's only hold if the inner TDef is resolved
Eq (Mu [] td {a = False}) where
  y == y' = eqMu [] td y y'

------ meta ----------

pow : Nat -> TDef' n a -> TDef' n a
pow  Z        _ = T1
pow (S Z)     a = a
pow (S (S n)) a = TProd (a :: a :: replicate n a)

powN : Nat -> TNamed' n a -> TDef' n a
powN n tn = pow n (wrap tn)

-- TODO add to stdlib?
minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     m    _   = rewrite minusZeroRight m in
                            plusZeroRightNeutral m
minusPlus (S _)  Z    lte = absurd lte
minusPlus (S n) (S m) lte = rewrite sym $ plusSuccRightSucc (m `minus` n) n in
                            cong $ minusPlus n m (fromLteSucc lte)

-- TODO add to stdlib
weakenLTE : Fin n -> LTE n m -> Fin m
weakenLTE  FZ     LTEZero impossible
weakenLTE (FS _)  LTEZero impossible
weakenLTE  FZ    (LTESucc y) = FZ
weakenLTE (FS x) (LTESucc y) = FS $ weakenLTE x y

mutual
  ||| Increase the type index representing the number of variables accessible
  ||| to a `TDef`, without actually changing the variables that are used by it.
  |||
  ||| @m The new amount of variables.
  weakenTDef : TDef' n a -> (m : Nat) -> LTE n m -> TDef' m a
  weakenTDef T0             _    _   = T0
  weakenTDef T1             _    _   = T1
  weakenTDef (TSum xs)      m    prf = TSum $ weakenTDefs xs m prf
  weakenTDef (TProd xs)     m    prf = TProd $ weakenTDefs xs m prf
  weakenTDef (TVar _)       Z    prf = absurd prf
  weakenTDef (TVar i)    (S m)   prf = TVar $ weakenLTE i prf
  weakenTDef (TMu xs)       m    prf = TMu $ weakenNTDefs xs (S m) (LTESucc prf)
  weakenTDef (TApp f xs)    m    prf = TApp f $ weakenTDefs xs m prf
  weakenTDef (RRef x)    (S m)   prf {a = False} = RRef $ weakenLTE x prf
  weakenTDef (FRef x)       m    prf {a = True } = FRef x

  weakenTDefs : Vect k (TDef' n a) -> (m : Nat) -> LTE n m -> Vect k (TDef' m a)
  weakenTDefs []      _ _   = []
  weakenTDefs (x::xs) m lte = weakenTDef x m lte :: weakenTDefs xs m lte

  weakenNTDefs : Vect k (Name, TDef' n a) -> (m : Nat) -> LTE n m -> Vect k (Name, TDef' m a)
  weakenNTDefs []          _ _   = []
  weakenNTDefs ((n,x)::xs) m lte = (n, weakenTDef x m lte) :: weakenNTDefs xs m lte

||| Increase the type index representing the number of variables accessible
||| to a `TNamed`, without actually changing the variables that are used by it.
|||
||| @m The new amount of variables.
weakenTNamed : TNamed' n a -> (m : Nat) -> LTE n m -> TNamed' m a
weakenTNamed (TName n t) m prf = TName n (weakenTDef t m prf)

-------- printing -------

mutual
  showTDef : TDef' n a -> String
  showTDef T0          = "0"
  showTDef T1          = "1"
  showTDef (TSum xs)   = parens $ showOp "+" xs
  showTDef (TProd xs)  = parens $ showOp "*" xs
  showTDef (TVar x)    = curly $ show $ toNat x
  showTDef (TMu ms)    = parens $ "mu " ++ square (showNTDefs ms)
  showTDef (TApp f []) = name f
  showTDef (TApp f xs) = parens $ concat (intersperse " " (name f :: map (assert_total showTDef) xs))
  showTDef (FRef n)    {a = True} = n
  showTDef (RRef n)    {a = False} = curly $ show $ toNat n

  showOp : String -> Vect k (TDef' n a) -> String
  showOp _  []         = ""
  showOp _  [x]        = showTDef x
  showOp op (x::y::ys) = showTDef x ++ " " ++ op ++ " " ++ showOp op (y::ys)

  showNTDefs : Vect k (Name, TDef' n a) -> String
  showNTDefs []          = ""
  showNTDefs [(n,x)]     = n ++ ": " ++ showTDef x
  showNTDefs ((n,x)::xs) = n ++ ": " ++ showTDef x ++ ", " ++ showNTDefs xs

showTNamed : TNamed' n a -> String
showTNamed (TName n t) = parens $ n ++ " := " ++ showTDef t

Show (TDef' n a) where
  show = showTDef

Show (TNamed' n a) where
  show = showTNamed

-- Equality -----

vectEq : Eq a => Vect n a -> Vect m a -> Bool
vectEq []      []      = True
vectEq (x::xs) (y::ys) = x == y && vectEq xs ys
vectEq _       _       = False

mutual

  heteroEq : {n, m : Nat} -> TDef' n a -> TDef' m a -> Bool
  heteroEq {n} {m} tn tm with (cmp n m)
    heteroEq {n}     tn tm | (CmpLT y) = tm == (weakenTDef tn _ (lteAddRight n)) -- or should this be `False`?
    heteroEq     {m} tn tm | (CmpGT x) = tn == (weakenTDef tm _ (lteAddRight m)) -- or should this be `False`?
    heteroEq         tn tm | (CmpEQ)   = tn == tm

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
