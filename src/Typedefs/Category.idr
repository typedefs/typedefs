
module Typedefs.Category

import Category
import Typedefs

%default total


||| A morphism between two typedefs.
record TDefMorphism (n : Nat) (a : TDef n) (b : TDef n) where
  constructor MkTDefMorphism
  f : (TDef n -> TDef n)
  app : b = f a

infixr 0 -&>

||| Morphism between two typedefs.
(-&>) : TDef n -> TDef n -> Type
(-&>) {n} x y = TDefMorphism n x y

tdefId : {n : Nat} -> (t : TDef n) -> t -&> t
tdefId t = MkTDefMorphism id Refl

infixr 7 -*-

||| Composition between two typedefs morphisms.
(-*-) : {n : Nat} -> {a, b, c : TDef n} -> (a -&> b) -> (b -&> c) -> (a -&> c)
(-*-) (MkTDefMorphism f pf1) (MkTDefMorphism g pf2) = rewrite pf2 in 
                                                      rewrite pf1 in MkTDefMorphism (g . f) Refl

tdefLeftId : (a, b : TDef n) -> (f : a -&> b) -> (tdefId a -*- f) = f
tdefLeftId k (m k) (MkTDefMorphism m Refl) = Refl

tdefRightId : (a, b : TDef n) -> (f : a -&> b) -> (f -*- tdefId b) = f
tdefRightId a (m a) (MkTDefMorphism m Refl) = Refl

tdefAssoc : (a, b, c, d : TDef n) 
  -> (f : a -&> b) -> (g : b -&> c) -> (h : c -&> d) 
  -> f -*- (g -*- h) = (f -*- g) -*- h
tdefAssoc a (ff a) (gg (ff a)) (hh (gg (ff a)))
  (MkTDefMorphism ff Refl) (MkTDefMorphism gg Refl) (MkTDefMorphism hh Refl) = Refl

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
