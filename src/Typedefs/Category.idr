
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

postulate funext : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

fundet : {f, g : a -> b} -> f = g -> (x : a) -> f x = g x
fundet Refl x = Refl

cong2 : {f : a -> b -> c} -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
cong2 Refl Refl = Refl

TypeCat : Category
TypeCat = typesAsCategory

-- @erik: http://docs.idris-lang.org/en/latest/reference/documenting.html#inline-documentation
-- ||| A data structure that associates a `Vect n Type` with another `Vect n Type`
-- ||| by pairing them up by index.
-- ||| TODO (So some sort of zip? actually is that some monoidal categorical thing going on?)
data TypeVect : (n : Nat) -> Vect n Type -> Vect n Type -> Type where
  NilTypeVect : TypeVect Z [] []
  ConsTypeVect : (a -> b) -> TypeVect m c d -> TypeVect (S m) (a :: c) (b :: d)

-- ||| Given a, a vector of types, and b another vector of types, contruct an
-- ||| indexed TypeVect using `a` and `b` as indexes.
TypeMorVect : (a, b : Vect n Type) -> Type
TypeMorVect a b {n} = TypeVect n a b

idVect : (v : Vect n Type) -> TypeMorVect v v
idVect [] = NilTypeVect
idVect (x :: xs) = ConsTypeVect (\ y => y) (idVect xs)

infixr 7 |*|

(|*|) : {a, b, c : Vect n Type} -> (f : TypeMorVect a b) -> (g : TypeMorVect b c) -> TypeMorVect a c
(|*|) {a=[]}    {b=[]}   {c=[]}     NilTypeVect        NilTypeVect       = NilTypeVect
(|*|) {a=x::xs} {b=y::d} {c=b::ys} (ConsTypeVect f z) (ConsTypeVect g w) = ConsTypeVect (g . f) (z |*| w)

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
  remapTypes  T0         x  y = y
  remapTypes  T1         x  y = y
  remapTypes (TSum xs)   x  y = remapEithers x xs y
  remapTypes (TProd xs)  x  y = remapPair x xs y
  remapTypes (TVar i)    fs y = remapTVar i fs y
  remapTypes (TMu xs)    fs y = remapMu (args xs) fs y
  remapTypes (TApp z xs) fs y = assert_total $ remapTypes (ap (def z) xs) fs y

mapMorphismsN : (tdef : TDef n) -> (a, b : Vect n Type) -> TypeMorVect a b -> TypeMorphism (Ty a tdef) (Ty b tdef)
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
  preserveIdMu a td (Inn y) = 
    cong $ 
    trans (cong {f = \ z => remapTypes td (ConsTypeVect z (idVect a)) y} (funext (assert_total $ preserveIdMu a td))) 
          (preserveIdN td ((Mu a td)::a) y)
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

mutual

  preserveComposeEithers : 
    (f : TypeVect n a b) ->
    (g : TypeVect n b c) ->
    (xs : Vect (S (S k)) (TDef n)) ->
    (\z => remapEithers (f |*| g) xs z) = (\x => remapEithers g xs (remapEithers f xs x))
  preserveComposeEithers {a} {b} {c} f g (z::w::[])    = funext $ \x => case x of 
    Left u => cong $ fundet (preserveComposeN z a b c f g) u
    Right v => cong $ fundet (preserveComposeN w a b c f g) v
  preserveComposeEithers {a} {b} {c} f g (z::w::s::xs) = funext $ \x => case x of 
    Left u => cong $ fundet (preserveComposeN z a b c f g) u
    Right v => cong $ fundet (preserveComposeEithers f g (w::s::xs)) v
  
  preserveComposePairs : 
    (f : TypeVect n a b) ->
    (g : TypeVect n b c) ->
    (xs : Vect (S (S k)) (TDef n)) ->
    (\z => remapPair (f |*| g) xs z) = (\x => remapPair g xs (remapPair f xs x))
  preserveComposePairs {a} {b} {c} f g (z::w::[])    = funext $ \(u,v) => 
    cong2 (fundet (preserveComposeN z a b c f g) u) (fundet (preserveComposeN w a b c f g) v)
  preserveComposePairs {a} {b} {c} f g (z::w::s::xs) = funext $ \(u,v) =>  
    cong2 (fundet (preserveComposeN z a b c f g) u) (fundet (preserveComposePairs f g (w::s::xs)) v) 
  
  preserveComposeTVar : 
    (f : TypeVect (S n) a b) ->
    (g : TypeVect (S n) b c) ->
    (i : Fin (S n)) ->
    (\z => remapTVar i (f |*| g) z) = (\x => remapTVar i g (remapTVar i f x))
  preserveComposeTVar         (ConsTypeVect f z) (ConsTypeVect g w)  FZ    = Refl
  preserveComposeTVar {n=S n} (ConsTypeVect f z) (ConsTypeVect g w) (FS i) = preserveComposeTVar z w i

  preserveComposeMu : 
    (f : TypeVect n a b) ->
    (g : TypeVect n b c) ->
    (xs : Vect k (String, TDef (S n))) ->
    (\z => remapMu (args xs) (f |*| g) z) = (\x => remapMu (args xs) g (remapMu (args xs) f x))
  preserveComposeMu {a} {b} {c} f g xs = funext $ \(Inn u) => 
    cong {f=Inn} $ 
    trans (fundet (cong {f=\z=>remapTypes (args xs) (ConsTypeVect z (f |*| g))} (assert_total $ preserveComposeMu f g xs)) u)
          (fundet (assert_total $ preserveComposeN (args xs) (Mu a (args xs)::a) (Mu b (args xs)::b) (Mu c (args xs)::c) (ConsTypeVect (remapMu (args xs) f) f) (ConsTypeVect (remapMu (args xs) g) g)) u) 

  preserveComposeN : (tdef : TDef n)
    -> (a, b, c : Vect n Type)
    -> (f : TypeVect n a b)
    -> (g : TypeVect n b c)
    -> (\z => remapTypes tdef (f |*| g) z) = (\x => remapTypes tdef g (remapTypes tdef f x))
  preserveComposeN T0          a b c f g = Refl 
  preserveComposeN T1          a b c f g = Refl
  preserveComposeN (TSum xs)   a b c f g = preserveComposeEithers f g xs
  preserveComposeN (TProd xs)  a b c f g = preserveComposePairs f g xs
  preserveComposeN (TVar i)    a b c f g = preserveComposeTVar f g i
  preserveComposeN (TMu xs)    a b c f g = preserveComposeMu f g xs
  preserveComposeN (TApp z xs) a b c f g = assert_total $ preserveComposeN (ap (def z) xs) a b c f g

||| The functor arising from a TDef between TypeCatN n and TypeCat
tdefCFunctor : (tdef : TDef n) -> CFunctor (TypeCatN n) TypeCat
tdefCFunctor tdef {n} = MkCFunctor (mapObjsN tdef) 
                                   (mapMorphismsN tdef) 
                                   (\a => funext (preserveIdN tdef a)) 
                                   (preserveComposeN tdef)
infixr 0 -&>

||| Morphism between two typedefs is a natural transformation between a TypeCatN and TypeCat.
(-&>) : TDef n -> TDef n -> Type
(-&>) {n} t s = NaturalTransformation (TypeCatN n) TypeCat (tdefCFunctor t) (tdefCFunctor s)

idComponent : (tdef : TDef n) -> (a : Vect n Type) -> TypeMorphism (Ty a tdef) (Ty a tdef)
idComponent _ _ ty = ty

idCommutative : (tdef : TDef n) 
             -> (a, b : Vect n Type) 
             -> (f : TypeMorVect a b) 
             -> (mapMorphismsN tdef a b f)
              . (idComponent tdef a)
              = (idComponent tdef b)
              . (mapMorphismsN tdef a b f)
idCommutative tdef a b f = Refl

tdefId : (t : TDef n) -> (t -&> t)
tdefId tdef = MkNaturalTransformation (idComponent tdef) (idCommutative tdef)

infixr 7 -*-

composeComponent : (f : a -&> b)
                -> (g : b -&> c)
                -> (v : Vect n Type)
                -> TypeMorphism (Ty v a) (Ty v c)
composeComponent (MkNaturalTransformation fComponent _)
                 (MkNaturalTransformation gComponent _)
                 v = gComponent v . fComponent v

composeCommutative : (f : a -&> b)
                  -> (g : b -&> c)
                  -> (v, w : Vect n Type)
                  -> (h : TypeVect n v w)
                  -> (\x => remapTypes c h (composeComponent f g v x))
                   = (\x => composeComponent f g w (remapTypes a h x))
composeCommutative (MkNaturalTransformation fcomponent fcompose)
                   (MkNaturalTransformation gcomponent gcompose)
                   v w h = ?whut

||| Composition between two typedefs morphisms.
(-*-) : {n : Nat} -> {a, b, c : TDef n} -> (a -&> b) -> (b -&> c) -> (a -&> c)
(-*-) f g {a} {b} {c} = MkNaturalTransformation (composeComponent f g) (composeCommutative f g)


tdefLeftId : (a, b : TDef n) -> (f : a -&> b) -> (tdefId a -*- f) = f

tdefRightId : (a, b : TDef n) -> (f : a -&> b) -> (f -*- tdefId b) = f

tdefAssoc : (a, b, c, d : TDef n)
  -> (f : a -&> b) -> (g : b -&> c) -> (h : c -&> d)
  -> f -*- (g -*- h) = (f -*- g) -*- h

||| The category of typedefs with n free variables.
||| Objects are typedefs, morphisms are Natural transformations between typedefs.
typedefsAsCategory : Nat -> Category
typedefsAsCategory n = MkCategory
  (TDef n)
  (-&>)
  (tdefId)
  (\a, b, c => (-*-) {a} {b} {c})
  (tdefLeftId)
  (tdefRightId)
  (tdefAssoc)
