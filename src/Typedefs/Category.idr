
module Typedefs.Category

import Category
import Typedefs
import Functor
import Data.Vect
import Names
import NaturalTransformation
import Idris.TypesAsCategory
import Idris.TypesAsCategoryExtensional
import Interfaces.Verified

%default total

TypeCat : Category
TypeCat = typesAsCategory

Arity : Nat -> Type
Arity n = Vect n Type

data TypeVect : (n : Nat) -> Vect n Type -> Vect n Type -> Type where
  NilTypeVect : TypeVect Z [] []
  ConsTypeVect : (a -> b) -> TypeVect m c d -> TypeVect (S m) (a :: c) (b :: d)

getVect : TypeVect n v1 v2 -> Vect n Type
getVect xs {v2} = v2

getVectProof : (xs : TypeVect n v1 v2) -> getVect xs = v2
getVectProof xs = Refl

TypeMorVect : (a, b : Vect n Type) -> Type
TypeMorVect a b {n} = TypeVect n a b

idVect : (v : Vect n Type) -> TypeMorVect v v
idVect [] = NilTypeVect
idVect (x :: xs) = ConsTypeVect id (idVect xs)

infixr 7 |*|

(|*|) : {a, b, c : Vect n Type} -> (f : TypeMorVect a b) -> (g : TypeMorVect b c) -> TypeMorVect a c
(|*|) {a = []} {b = []} {c = []} NilTypeVect NilTypeVect = NilTypeVect
(|*|) {a = (x :: xs)} {b = (y :: d)} {c = (b :: ys)} (ConsTypeVect f z) (ConsTypeVect g w) = ConsTypeVect (g . f) (z |*| w)

leftIdVect : (a, b : Vect n Type) -> (f : TypeMorVect a b) -> (idVect a) |*| f = f
leftIdVect [] [] NilTypeVect = Refl
leftIdVect (x :: c) (y :: d) (ConsTypeVect f z) = cong $ leftIdVect c d z

rightIdVect : (a, b : Vect n Type) -> (f : TypeMorVect a b) -> f |*| (idVect b) = f
rightIdVect [] [] NilTypeVect = Refl
rightIdVect (x :: c) (y :: d) (ConsTypeVect f z) = cong $ rightIdVect c d z

assocVect :
     (a, b, c, d : Vect n Type) 
  -> (f : TypeMorVect a b) 
  -> (g : TypeMorVect b c) 
  -> (h : TypeMorVect c d) 
  -> f |*| (g |*| h) = (f |*| g) |*| h

TypeCatN : Nat -> Category
TypeCatN n = MkCategory
  (Vect n Type)
  TypeMorVect
  idVect
  (\a, b, c => (|*|) {a} {b} {c})
  leftIdVect
  rightIdVect
  assocVect

mapObjsN : TDef n -> Vect n Type -> Type
mapObjsN = flip Ty

remapEithers : TypeVect n v1 v2 -> (xs : Vect (S (S k)) (TDef n)) -> Tnary v1 xs Either -> Tnary v2 xs Either
remapEithers x (z :: (w :: [])) y = either ?remapLeft ?remapRight y
remapEithers x (z :: (w :: (s :: xs))) y = either ?remapLeft2 ?remapRight2 y

remapPair : TypeVect n v1 v2 -> (xs : Vect (S (S k)) (TDef n)) -> Tnary v1 xs Pair -> Tnary v2 xs Pair
remapPair x (z :: (w :: [])) y = (?remapPairLeft, ?remapPairRight)
remapPair x (z :: (w :: (s :: xs))) y = (?remapPairLeft2, ?remapPairRight2)

remapTypes : {n : Nat} -> {v1, v2 : Vect n Type} -> (tdef : TDef n) 
  -> TypeMorVect v1 v2 -> Ty v1 tdef -> Ty v2 tdef
remapTypes T0 x y = y
remapTypes T1 x y = y
remapTypes (TSum xs) x y = remapEithers x xs y
remapTypes (TProd xs) x y = remapPair x xs y
remapTypes (TVar FZ) (ConsTypeVect f x) y = f y
remapTypes (TVar (FS FZ)) (ConsTypeVect f (ConsTypeVect g x)) y = g y
remapTypes (TVar (FS (FS z))) (ConsTypeVect f x) y = remapTypes (TVar (FS z)) (?tvect) ?remapVarbbb
remapTypes (TMu xs) mor y = ?remapTypes_rhs_6
remapTypes (TApp z xs) mor y = ?remapTypes_rhs_7

mapMorphismsN : (tdef : TDef n) -> (a, b : Vect n Type) -> TypeMorVect a b -> TypeMorphism (mapObjsN tdef a) (mapObjsN tdef b)
mapMorphismsN tdef a b mor = remapTypes {v1=a} {v2=b} tdef mor

preserveIdN : (tdef : TDef n) -> (a : Vect n Type) -> remapTypes tdef (idVect a) = Prelude.Basics.id
preserveIdN tdef a = ?preserveIdN_rhs

preserveComposeN : (tdef : TDef n) 
  -> (a, b, c : Vect n Type) 
  -> (f : TypeVect n a b) 
  -> (g : TypeVect n b c) 
  -> remapTypes tdef (f |*| g) = (\x => remapTypes tdef g (remapTypes tdef f x))

tdefCFunctor : (tdef : TDef n) -> CFunctor (TypeCatN n) Idris.TypesAsCategory.typesAsCategory
tdefCFunctor tdef {n} = MkCFunctor (mapObjsN tdef) (mapMorphismsN tdef) (preserveIdN tdef) (preserveComposeN tdef)

infixr 0 -&>

record TypedTDef (n : Nat) (tdef : TDef n) where
  constructor MkTypedTDef
  apply : (args : Vect n Type) -> Ty args tdef

pureTDef : (tdef : TDef n) -> TypedTDef n tdef

||| Morphism between two typedefs.
(-&>) : TDef n -> TDef n -> Type
-- (-&>) {n} a b = NaturalTransformation _ _ [| a |] [| b|]

tdefId : {n : Nat} -> (t : TDef n) -> t -&> t

infixr 7 -*-

||| Composition between two typedefs morphisms.
(-*-) : {n : Nat} -> {a, b, c : TDef n} -> (a -&> b) -> (b -&> c) -> (a -&> c)

tdefLeftId : (a, b : TDef n) -> (f : a -&> b) -> (tdefId a -*- f) = f

tdefRightId : (a, b : TDef n) -> (f : a -&> b) -> (f -*- tdefId b) = f

tdefAssoc : (a, b, c, d : TDef n) 
  -> (f : a -&> b) -> (g : b -&> c) -> (h : c -&> d) 
  -> f -*- (g -*- h) = (f -*- g) -*- h

||| The category of typedefs with n free variables.
||| Objects are typedefs, morphisms are functions between typedefs.
typedefsAsCategory : Nat -> Category
typedefsAsCategory n = MkCategory
  (TDef n)
  (-&>)
  (tdefId)
  (\a, b, c => (-*-) {a} {b} {c})
  (tdefLeftId)
  (tdefRightId)
  (tdefAssoc)
