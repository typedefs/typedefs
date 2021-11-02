module Typedefs.Idris

import Data.Vect

import Typedefs.Names
import Typedefs
import public Typedefs.DependentLookup
import public Typedefs.DecEq

%default total

public export
Constructor : Nat -> Type -> Type
Constructor Z ret = ret
Constructor (S n) ret = Type -> Constructor n ret

public export
TypeConstructor : Nat -> Type
TypeConstructor Z = Type
TypeConstructor (S n) = Type -> TypeConstructor n

public export 0
ApplyVect : TypeConstructor n -> (0 _ : Vect n Type) -> Type
ApplyVect c [] = c
ApplyVect c (x :: xs) {n = S k} = ApplyVect (c x) xs

||| A mapping from TDef to idris Type constructor
public export
SpecialList : Nat -> Type
SpecialList n = Vect n (v ** (TDefR v, TypeConstructor v))

public export
args : {k : Nat} -> Vect k (String, TDef' (S n) a) -> TDef' (S n) a
args []                 = T0
args [(_,m)]            = m
args ((_,m)::(_,l)::ms) = TSum (m :: l :: map snd ms)

public export
ReverseVect : {n : Nat} -> (mkType : Vect n Type -> Type) -> TypeConstructor n
ReverseVect mkType {n = Z} = mkType []
ReverseVect mkType {n = (S k)} = \arg => ReverseVect (popHead mkType arg)
  where
    popHead : (Vect (S n) Type -> Type) -> Type -> Vect n Type -> Type
    popHead f t ts = f (t :: ts)

mutual
  public export
  data Mu' : {n : Nat} -> (sp : SpecialList l) -> (tvars : Vect n Type) -> TDef' (S n) a -> Type where
    Inn : Lazy (Ty' sp (Mu' sp tvars m :: tvars) m) -> Mu' sp tvars m

  public export 0
  Tnary' : {n : Nat} -> (sp : SpecialList l) -> (tvars : Vect n Type) -> Vect (2 + k) (TDefR n) -> (Type -> Type -> Type) -> Type
  Tnary' sp tvars [x, y]              c = c (Ty' sp tvars x) (Ty' sp tvars y)
  Tnary' sp tvars (x :: y :: z :: zs) c = c (Ty' sp tvars x) (Tnary' sp tvars (y :: z :: zs) c)

  ||| Interpret a TDef into an Idris type
  |||
  ||| The replacement mapping can only replace types in Mu or App Position.
  ||| Products, Sums, 0, 1 and variables are never replaced.
  |||
  ||| @sp : The mapping between TDefs and the specialised version as an Idris type
  ||| @tvars : The list of types that will be used to fill all free variables
  public export 0
  Ty' : {n : Nat} -> (sp : SpecialList l) -> (tvars : Vect n Type) ->  TDefR n -> Type
  Ty' sp tvars T0             = Void
  Ty' sp tvars T1             = Unit
  Ty' sp tvars (TSum xs) {n}  = assert_total $ Tnary' sp tvars xs Either
  Ty' sp tvars (TProd xs) {n} = assert_total $ Tnary' sp tvars xs Pair
  Ty' sp tvars (TVar v)       = Vect.index v tvars
  Ty' sp tvars (RRef i)       = Vect.index i tvars
  Ty' sp tvars (TMu m) = case (depLookup sp (TMu m)) of
    Nothing => assert_total $ Mu' sp tvars (args m)
    Just (_ ** constr ** prf) => ApplyVect constr tvars

  -- For application we first make a lookup in our mapping from TDef to Type constructors
  Ty' sp tvars (TApp name xs) with (depLookup sp name.def)
    -- If we can't find anything, simply apply the type normally
    Ty' sp tvars (TApp name xs) | Nothing = assert_total $ Ty' sp tvars $ name.def `ap` xs
    -- If we find a match, check the length of the arguments match the arity of the type constructor
    -- we found.
    Ty' sp tvars (TApp name xs) | Just (arity ** constr ** prf) =
        let args = map (assert_total $ Ty' sp tvars) xs in ApplyVect constr args

{-
-- extractMu : {n,k : Nat} -> {sp : SpecialList l} -> {0 ts : Vect n Type} -> {td : Vect k (String, TDefR (S n))} ->
--             (prf : depLookup sp (TMu td) = Nothing) ->
--             Ty' sp ts (TMu td) -> Ty' sp (Ty' [] ts (TMu td) :: ts) (args td)
-- extractMu Refl x = ?extractMu_rhs

-- for some reason this property does not reduce in `TermWrite.idr` even after a `with (depLookup [] (TMu td))`
public export
TyMuPrf : {n, k : Nat} -> {ts : Vect n Type} -> (td : Vect k (String, TDefR (S n) )) -> Ty' [] ts (TMu td) = Mu' [] ts (args td)
TyMuPrf td = believe_me $ Refl {x=Mu' [] ts (args td)}

public export 0
Ty : {n : Nat} -> (tvars : Vect n Type) -> TDefR n -> Type
Ty = Ty' []

public export 0
Tnary : {n : Nat} -> Vect n Type -> Vect (2 + k) (TDefR n) -> (Type -> Type -> Type) -> Type
Tnary tvars tds op = Tnary' [] tvars tds op

public export
Mu : {n : Nat} -> Vect n Type -> TDef' (S n) a -> Type
Mu args td = Mu' [] args td

public export
Inn' : Ty (Mu tvars m :: tvars) m -> Mu tvars m
Inn' v = Inn (believe_me v)

Const1 : a -> b -> a
Const1 v _ = v

Const2 : a -> b -> c -> a
Const2 v _ _ = v

public export 0
Const : (n : Nat) -> Type -> Type
Const Z ty = ty
Const (S n) ty = forall x. x -> Const n ty

public export
ConstN : (n : Nat) -> (v : Type) -> TypeConstructor n
ConstN Z ty = ty
ConstN (S n) ty = \_ => ConstN n ty

||| Converts a typedefs of `n` free variables into a type constructor that expects n arguments
public export 0
AlphaTy : {n : Nat} -> (sp : SpecialList l) -> TDefR n -> TypeConstructor n
AlphaTy sp tdef = ReverseVect (\args =>  Ty' sp args tdef)

public export
NatSum : {f : Nat -> Type} -> Vect n (k : Nat ** f k) -> Nat
NatSum [] = Z
NatSum ((x ** _) :: xs) = x + NatSum xs

public export 0
constructTypes : (types : Vect n (k ** TypeConstructor k)) -> Vect (NatSum types) Type -> Vect n Type
constructTypes [] [] = []
constructTypes ((k ** tc) :: xs) args =
  let (pre, post) = splitAt k args
   in ApplyVect tc pre :: constructTypes xs post

||| Given a vector of type constructors and a TDef construct the Idris type
||| from it using the second vector to instanciate the constructors
public export 0
BetaTy : {n : Nat} -> (types : Vect n (k ** TypeConstructor k)) -> TDefR n
     -> Vect (NatSum types) Type -> Type
BetaTy types tdef args = Ty' [] (constructTypes types args) tdef

||| Given a list of type constructors fill the holes with them and return a new type constructor
public export 0
GammaTy : {n : Nat} -> (types : Vect n (k ** TypeConstructor k)) -> TDefR n
     -> TypeConstructor (NatSum types)
GammaTy types tdef = ReverseVect {n=NatSum types} (BetaTy types tdef)


---------------------------------------------------------------------------------------------
-- Lemmas                                                                                  --
---------------------------------------------------------------------------------------------

-- ||| Since `convertTy` is an identity function it is safe to assume this one is too
-- 0
-- convertTy' : Ty' [] ts (TApp f ys) -> Ty' [] ts (ap (def f) ys)
-- convertTy' x = believe_me x
--
-- -- `showTy` just needs a little nudge in the right direction
-- 0
-- convertTy : {n : Name} -> Ty' [] v (TApp (TName n def) xs) -> Ty' [] v (def `ap` xs)
-- convertTy x {def = T0       } = x
-- convertTy x {def = T1       } = x
-- convertTy x {def = TSum xs  } = x
-- convertTy x {def = TProd xs } = x
-- convertTy x {def = TVar i   } = x
-- convertTy x {def = TMu xs   } = x
-- convertTy x {def = TApp y xs} = x
-- convertTy x {def = RRef y   } = x

-- ||| Convert an `ap` into a `TApp` however the replacement context needs to be empty
-- convertPrf : Ty' [] v (ap def xs) = Ty' [] v (TApp (TName n def) xs)
-- convertPrf {def = T0} = Refl
-- convertPrf {def = T1} = Refl
-- convertPrf {def = (TSum xs)} = Refl
-- convertPrf {def = (TProd xs)} = Refl
-- convertPrf {def = (TVar i)} = Refl
-- convertPrf {def = (TMu xs)} = Refl
-- convertPrf {def = (RRef x)} = Refl
-- convertPrf {def = (TApp x xs)} = Refl

-- TODO we should either finish mu/app cases or save some space by
-- making both of these into `really_believe_me` one-liners.
-- This is safe because adding/removing an unused var is a no-op.

-- ignoreShift : {t : TDefR n} -> Ty' sp (var::vars) (shiftVars t) -> Ty' sp vars t
-- ignoreShift {t=T0}                     ty         = absurd ty
-- ignoreShift {t=T1}                     ()         = ()
-- ignoreShift {t=TSum [x,y]}             (Left ty)  = Left $ ignoreShift ty
-- ignoreShift {t=TSum [x,y]}             (Right ty) = Right $ ignoreShift ty
-- ignoreShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ ignoreShift ty
-- ignoreShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ ignoreShift {t=TSum (y::z::ts)} ty
-- ignoreShift {t=TProd [x,y]}            (ty1,ty2)  = (ignoreShift ty1,ignoreShift ty2)
-- ignoreShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (ignoreShift ty1,ignoreShift {t=TProd (y::z::ts)} ty2)
-- ignoreShift {t=TMu cs}                  ty        = really_believe_me ty
-- ignoreShift {t=TApp (TName nam df) xs}  ty        = really_believe_me ty
-- ignoreShift {t=TVar v}                  ty        = ty
-- ignoreShift {t=RRef i}                  ty        = ty
--
-- addShift : {t : TDefR n} -> Ty' sp vars t -> Ty' sp (var::vars) (shiftVars t)
-- addShift {t=T0}                      ty        = absurd ty
-- addShift {t=T1}                     ()         = ()
-- addShift {t=TSum [x,y]}             (Left ty)  = Left $ addShift ty
-- addShift {t=TSum [x,y]}             (Right ty) = Right $ addShift ty
-- addShift {t=TSum (x::y::z::ts)}     (Left ty)  = Left $ addShift ty
-- addShift {t=TSum (x::y::z::ts)}     (Right ty) = Right $ addShift {t=TSum (y::z::ts)} ty
-- addShift {t=TProd [x,y]}            (ty1,ty2)  = (addShift ty1,addShift ty2)
-- addShift {t=TProd (x::y::z::ts)}    (ty1,ty2)  = (addShift ty1,addShift {t=TProd (y::z::ts)} ty2)
-- addShift {t=TMu cs}                  ty        = really_believe_me ty
-- addShift {t=TApp (TName nam df) xs}  ty        = really_believe_me ty
-- addShift {t=TVar v}                  ty        = ty
-- addShift {t=RRef i}                  ty        = ty

-------------------------------------------------------------------------------
-- Show                                                                      --
-------------------------------------------------------------------------------

-- mutual
--
--   showMu : (tvars : Vect n (a : Type ** a -> String)) -> (td : TDef' (S n) b)
--         -> Mu' [] (map DPair.fst tvars) td -> String
--   showMu tvars td (Inn x) =
--     let printMu = (Mu' [] (map DPair.fst tvars) td ** assert_total $ showMu tvars td)
--      in parens' (assert_total $ showTy (printMu::tvars) td x)
--
--   ||| Print the content of a TDef provided functions to display Types as strings
--   ||| @tvars a vector of n functions that map types to their string representation
--   ||| @td the tdef to show
--   ||| @x the idris type represented by `td` using `tvars` for free variables
--   showTy : (tvars : Vect n (a : Type ** a -> String))
--         -> (td : TDefR n)
--         -> (x : Ty' [] (map DPair.fst tvars) td)
--         -> String
--   showTy                  tvars  T0                          x        impossible
--   showTy                  tvars  T1                          x        = show x
--   showTy                  tvars  (TSum [a,b])               (Left x)  = "Left " ++ parens' (showTy tvars a x)
--   showTy                  tvars  (TSum [a,b])               (Right x) = "Right " ++ parens' (showTy tvars b x)
--   showTy                  tvars  (TSum (a::b::c::xs))       (Left x)  = "Left " ++ parens' (showTy tvars a x)
--   showTy                  tvars  (TSum (a::b::c::xs))       (Right x) = "Right " ++ parens' (assert_total $ showTy tvars (TSum (b::c::xs)) x)
--   showTy   ((a ** showA)::tvars) (TVar FZ)                   x        = showA x
--   showTy {n=S (S n')} (_::tvars) (TVar (FS i))               x        = showTy {n = S n'} tvars (TVar i) x
--   showTy                  tvars  (TMu m)                     x        = showMu tvars (args m) x
--   showTy   ((a ** showA)::tvars) (RRef FZ)                   x        = showA x
--   showTy {n=S (S n')} (_::tvars) (RRef (FS i))               x        = showTy {n = S n'} tvars (RRef i) x
--   showTy                  tvars  (TApp (TName name def) xs)  x
--     = assert_total $ showTy tvars (def `ap` xs) (convertTy x)
--   showTy {n}              tvars  (TProd xs)                  x
--     = parens $ concat $ List.intersperse ", " (showProd xs x)
--     where showProd : (ys : Vect (2 + k) (TDefR n))
--                   -> Tnary' [] (map DPair.fst tvars) ys Pair -> List String
--           showProd [a, b]        (x, y) = (showTy tvars a x)::[showTy tvars b y]
--           showProd (a::b::c::ys) (x, y) = (showTy tvars a x)::showProd (b::c::ys) y
--
-- Show (Mu' sp {l=Z} [] td) where
--   show y {sp=[]} = showMu [] td y
--
-- -------------------------------------------------------------------------------
-- -- Type Equality                                                             --
-- -------------------------------------------------------------------------------
-- -- Note: Equality on Types only work when the specialisation context is empty--
-- -------------------------------------------------------------------------------
--
-- mutual
--
--   eqMu : (tvars : Vect n (a : Type ** a -> a -> Bool)) -> (td : TDefR (S n)) ->
--          Mu' [] (map DPair.fst tvars) td -> Mu' [] (map DPair.fst tvars) td  -> Bool
--   eqMu tvars td (Inn x) (Inn x') =
--     eqTy ((Mu' [] (map DPair.fst tvars) td ** assert_total $ eqMu tvars td)::tvars) td x x'
--
--   eqTy : (tvars : Vect n (a : Type ** a -> a -> Bool)) -> (td : TDefR n) ->
--          Ty' [] (map DPair.fst tvars) td -> Ty' [] (map DPair.fst tvars) td -> Bool
--   eqTy tvars T0                    x x'        impossible
--   eqTy tvars T1                    x x'      = x == x'
--   eqTy tvars (TSum [a,b])          (Left x)  (Left x') = eqTy tvars a x x'
--   eqTy tvars (TSum [a,b])          (Right x) (Right x') = eqTy tvars b x x'
--   eqTy tvars (TSum (a::b::c::xs))  (Left x)  (Left x') = eqTy tvars a x x'
--   eqTy tvars (TSum (a::b::c::xs))  (Right x) (Right x') = assert_total $ eqTy tvars (TSum (b::c::xs))  x x'
--   eqTy {n = n} tvars (TProd xs)    x x' = eqProd xs x x'
--     where eqProd : (ys : Vect (2 + k) (TDefR n))
--                 -> Tnary' [] (map DPair.fst tvars) ys Pair
--                 -> Tnary' [] (map DPair.fst tvars) ys Pair -> Bool
--           eqProd [a, b]        (x, y) (x', y') = (eqTy tvars a x x') && (eqTy tvars b y y')
--           eqProd (a::b::c::ys) (x, y) (x', y') = (eqTy tvars a x x') && (eqProd (b::c::ys) y y')
--   eqTy ((a ** eqA)::tvars)     (TVar FZ)         x x' = eqA x x'
--   eqTy {n = S (S n')} (_::tvars) (TVar (FS i))   x x' = eqTy {n = S n'} tvars (TVar i) x x'
--   eqTy tvars                     (TMu m)         x x' = eqMu tvars (args m) x x'
--   eqTy tvars      (TApp (TName name def) xs)     x x' = assert_total $ eqTy tvars (def `ap` xs) (convertTy x) (convertTy x')
--   eqTy ((a ** eqA)::tvars)       (RRef FZ)       x x' = eqA x x'
--   eqTy {n = S (S n')} (_::tvars) (RRef (FS i))   x x' = eqTy {n = S n'} tvars (RRef i) x x'
--   eqTy tvars _ _ _ = False
--
-- ||| Equality instance for Mu's only hold if the inner TDef is resolved
-- Eq (Mu' sp {l=Z} [] td {a = False}) where
--   (==) y y' {sp=[]} = eqMu [] td y y'
{-
-}
