module Typedefs.Equality



%access public export

(DecEq a, (y : a) -> DecEq (p y)) => DecEq (DPair a p) where
  decEq @{da} @{dp} (x ** y) (z ** w) with (decEq x z)
    decEq @{da} @{dp} (x ** y) (x ** w) | Yes Refl with (decEq @{dp x} y w)
      decEq (x ** y) (x ** y) | Yes Refl | Yes Refl = Yes Refl
      decEq (x ** y) (x ** w) | Yes Refl | No neq = No (\Refl => neq Refl)
    | No neq = No (\q => neq (cong {f = DPair.fst} q))

(DecEq a, {y : a} -> Eq (p y)) => Eq (DPair a p) where
  (==) (f ** fp) (s ** sp) with (decEq f s)
    (==) (f ** fp) (f ** sp) | Yes Refl = fp == sp
    (==) (f ** fp) (s ** sp) | No _ = False

