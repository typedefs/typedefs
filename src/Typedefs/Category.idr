
module Typedefs.Category

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Typedefs
import Data.Vect
import Names
import Idris.TypesAsCategory
import Idris.TypesAsCategoryExtensional
import Interfaces.Verified

%default total

functionExtensionality : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g
functionExtensionality fxgx = really_believe_me fxgx

cong2 : {f : a -> b -> c} -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
cong2 Refl Refl = Refl

TypeCat : Category
TypeCat = typesAsCategory

data TypeVect : (n : Nat) -> Vect n Type -> Vect n Type -> Type where
  NilTypeVect : TypeVect Z [] []
  ConsTypeVect : (a -> b) -> TypeVect m c d -> TypeVect (S m) (a :: c) (b :: d)

||| Given a, a vector of types, and b another vector of types, contruct an
||| indexed TypeVect using `a` and `b` as indexes.
TypeMorVect : (a, b : Vect n Type) -> Type
TypeMorVect a b {n} = TypeVect n a b

idVect : (v : Vect n Type) -> TypeMorVect v v
idVect [] = NilTypeVect
idVect (x :: xs) = ConsTypeVect (\ y => y) (idVect xs)

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
     {a, b, c, d : Vect n Type}
  -> (f : TypeMorVect a b)
  -> (g : TypeMorVect b c)
  -> (h : TypeMorVect c d)
  -> f |*| (g |*| h) = (f |*| g) |*| h
assocVect NilTypeVect NilTypeVect NilTypeVect = Refl
assocVect (ConsTypeVect f fs) (ConsTypeVect g gs) (ConsTypeVect h hs) =
  rewrite assocVect fs gs hs in Refl

TypeCatN : Nat -> Category
TypeCatN n = MkCategory
  (Vect n Type)
  TypeMorVect
  idVect
  (\a, b, c => (|*|) {a} {b} {c})
  leftIdVect
  rightIdVect
  (\a, b, c, d => assocVect)

mapObjsN : TDef n -> Vect n Type -> Type
mapObjsN = flip Ty


mutual

  remapEithers : TypeVect n v1 v2 -> (xs : Vect (S (S k)) (TDef n)) -> Tnary v1 xs Either -> Tnary v2 xs Either
  remapEithers fs (z::w::[])    (Left y)  = Left  (remapTypes z fs y)
  remapEithers fs (z::w::[])    (Right y) = Right (remapTypes w fs y)
  remapEithers fs (z::w::s::xs) (Left y)  = Left  (remapTypes z fs y)
  remapEithers fs (z::w::s::xs) (Right y) = Right (remapEithers fs (w::s::xs) y)

  remapPair : TypeVect n v1 v2 -> (xs : Vect (S (S k)) (TDef n)) -> Tnary v1 xs Pair -> Tnary v2 xs Pair
  remapPair fs (z::w::[])    (a, b) = (remapTypes z fs a, remapTypes w fs b)
  remapPair fs (z::w::s::xs) (a, b) = (remapTypes z fs a, remapPair fs (w::s::xs) b)

  remapTVar : (i : Fin n) -> TypeVect n v1 v2 -> index i v1 -> index i v2
  remapTVar FZ     (ConsTypeVect f fs) y = f y
  remapTVar (FS i) (ConsTypeVect f fs) y = remapTVar i fs y

  remapMu : (td : TDef (S n)) -> TypeVect n v1 v2 -> Mu v1 td -> Mu v2 td
  remapMu td fs (Inn y) = Inn (remapTypes td (ConsTypeVect (assert_total $ remapMu td fs) fs) y)

  remapTypes : {n : Nat} -> {v1, v2 : Vect n Type} -> (tdef : TDef n) ->
               TypeMorVect v1 v2 -> Ty v1 tdef -> Ty v2 tdef
  remapTypes T0 x y = y
  remapTypes T1 x y = y
  remapTypes (TSum xs) x y = remapEithers x xs y
  remapTypes (TProd xs) x y = remapPair x xs y
  remapTypes (TVar i) fs y = remapTVar i fs y
  remapTypes (TMu xs) fs y = remapMu (args xs) fs y
  remapTypes (TApp z xs) fs y = assert_total $ remapTypes (ap (def z) xs) fs y

mapMorphismsN : (tdef : TDef n) -> (a, b : Vect n Type) -> TypeMorVect a b -> TypeMorphism (mapObjsN tdef a) (mapObjsN tdef b)
mapMorphismsN tdef a b mor = remapTypes {v1=a} {v2=b} tdef mor

mutual

  preserveIdEithers : (a : Vect n Type) -> (xs : Vect (S (S k)) (TDef n)) ->
                      (y : Tnary a xs Either) -> remapEithers (idVect a) xs y = y
  preserveIdEithers a (z::w::[])    (Left y)  = cong (preserveIdN z a y)
  preserveIdEithers a (z::w::[])    (Right y) = cong (preserveIdN w a y)
  preserveIdEithers a (z::w::s::xs) (Left y)  = cong (preserveIdN z a y)
  preserveIdEithers a (z::w::s::xs) (Right y) = cong (preserveIdEithers a (w::s::xs) y)

  preserveIdPair : (a : Vect n Type) -> (xs : Vect (S (S k)) (TDef n)) ->
                   (y : Tnary a xs Pair) -> remapPair (idVect a) xs y = y
  preserveIdPair fs (z::w::[])    (a, b) = cong2 (preserveIdN z fs a) (preserveIdN w fs b)
  preserveIdPair fs (z::w::s::xs) (a, b) = cong2 (preserveIdN z fs a) (preserveIdPair fs (w::s::xs) b)


  preserveIdTVar : (a : Vect n Type) -> (i : Fin n) ->
                   (y : index i a) -> remapTVar i (idVect a) y = y
  preserveIdTVar (_::_) FZ     y = Refl
  preserveIdTVar (_::a) (FS i) y = preserveIdTVar a i y

  preserveIdMu : (a : Vect n Type) -> (td : TDef (S n)) ->
                 (y : Mu a td) -> remapMu td (idVect a) y = y
  preserveIdMu a td (Inn y) = cong (trans (cong {f = \ z => remapTypes td (ConsTypeVect z (idVect a)) y} (functionExtensionality (assert_total $ preserveIdMu a td))) (preserveIdN td ((Mu a td)::a) y))
  -- To do this properly: prove the property for any fs *extensionally
  -- equal to* idVect a


  preserveIdN : (tdef : TDef n) -> (a : Vect n Type) ->
                (y : Ty a tdef) -> remapTypes tdef (idVect a) y = y
  preserveIdN T0 a y = Refl
  preserveIdN T1 a y = Refl
  preserveIdN (TSum xs) a y = preserveIdEithers a xs y
  preserveIdN (TProd xs) a y = preserveIdPair a xs y
  preserveIdN (TVar i) a y = preserveIdTVar a i y
  preserveIdN (TMu xs) a y = preserveIdMu a (args xs) y
  preserveIdN (TApp z xs) a y = assert_total $ preserveIdN (ap (def z) xs) a y

preserveComposeN : (tdef : TDef n)
  -> (a, b, c : Vect n Type)
  -> (f : TypeVect n a b)
  -> (g : TypeVect n b c)
  -> remapTypes tdef (f |*| g) = (\x => remapTypes tdef g (remapTypes tdef f x))

||| The functor arising from a TDef between TypeCatN n and TypeCat
tdefCFunctor : (tdef : TDef n) -> CFunctor (TypeCatN n) TypeCat
tdefCFunctor tdef {n} = MkCFunctor (mapObjsN tdef) 
                                   (mapMorphismsN tdef) 
                                   (\a => functionExtensionality (preserveIdN tdef a)) 
                                   (preserveComposeN tdef)

infixr 0 -&>

||| Morphism between two typedefs is a natural transformation between a TypeCatN and TypeCat.
(-&>) : TDef n -> TDef n -> Type
(-&>) {n} t s = NaturalTransformation (TypeCatN n) TypeCat (tdefCFunctor t) (tdefCFunctor s)

idComponents : (tdef : TDef n) -> (a : Vect n Type) 
  -> TypeMorphism (Ty a tdef) (Ty a tdef)
idComponents _ _ ty = ty

idCommutative : (tdef : TDef n) 
  -> (a, b : Vect n Type)
  -> (f : TypeVect n a b)
  -> (mapMorphismsN tdef a b f) . (idComponents tdef a)
   = (idComponents tdef b) . (mapMorphismsN tdef a b f)

tdefId : (t : TDef n) -> (t -&> t)
tdefId {n} tdef = MkNaturalTransformation (idComponents tdef) (idCommutative tdef)

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
