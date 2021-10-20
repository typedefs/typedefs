module Typedefs.Containers

import Data.Container
import Data.Vect
import Data.Nat
import Control.Relation
import Typedefs
import Typedefs.Idris

record Iso (a, b : Type) where
  constructor MkIso
  from : b -> a
  to : a -> b
  fromTo : (v : a) -> from (to v) = v
  toFrom : (v : b) -> to (from v) = v

Fn : Type -> Type -> Type
Fn a b = a -> b

minusSucc : (a, b : Nat) -> a `minus` b = S a `minus` S b
minusSucc a 0 = Refl
minusSucc a (S k) = Refl

minusPrf : b `LTE` a -> c + (minus a b) = minus (c + a) b
minusPrf LTEZero = rewrite minusZeroRight a in
                   rewrite minusZeroRight (c + a) in Refl
minusPrf (LTESucc x {left} {right}) =
  minusPrf {c} x `trans` (rewrite sym (plusSuccRightSucc c right) in Refl)

0 ToTy : (n : Nat) -> TDefR m -> Vect (m `minus` n) Type -> {auto check : n `LTE` m} -> Type
ToTy 0 x tys = let tys' = replace {p= \x => Vect x Type} (minusZeroRight m) tys in Ty' [] tys' x
ToTy (S k) x tys = (ty : Type) -> case check of
                                       (LTESucc y) => let ty' = replace {p= \x => Vect x Type} (minusPrf {c=1} y) (ty :: tys)
                                                       in ToTy k x ty' {check=lteSuccRight y}

-- The positions of a coproduct is the selection of which tdef to pick
0 SumPos : {n : Nat} -> Vect k (TDefR n) -> Fin k -> Type
SumPos xs x = let td = index x xs in ToTy n td (rewrite sym $ minusZeroN n in []) {check = reflexive {x=n} {rel=LTE}}

0 TDefToCont : TDefR Z -> Container
TDefToCont T0 = MkContainer Void absurd
TDefToCont T1 = MkContainer Unit (const Unit)
-- TDefToCont (TSum {k} xs) = MkContainer (Fin (S (S k))) (SumPos xs)
TDefToCont (TSum [c1, c2]) = Combinators.Sum (TDefToCont c1) (TDefToCont c2)
TDefToCont (TSum (c1 :: c2 :: c3 :: cs)) = Combinators.Sum (TDefToCont c1) (TDefToCont (TProd (c2 :: c3 :: cs)))
TDefToCont (TProd [c1, c2]) = Combinators.Pair (TDefToCont c1) (TDefToCont c2)
TDefToCont (TProd (c1 :: c2 :: c3 :: cs)) = Combinators.Pair (TDefToCont c1) (TDefToCont (TProd (c2 :: c3 :: cs)))
-- TDefToCont (TVar i) = ?TDefToCont_rhs_5
TDefToCont (TMu xs) = ?TDefToCont_rhs_6
TDefToCont (TApp x xs) = let v = def x `ap` xs in TDefToCont v

-- ListT = Mu [("nil", t1), ("cons", Var1)]




record Lens (a, b, s, t : Type) where

LensToMor : (a, b : TDef' n m)
         -> Lens (Ty' sp args ty) (Ty' sp args tya) (Ty' sp args tyb) (Ty' sp args tyb)
         -> Morphism (TDefToCont tya) (TDefToCont tyb)
