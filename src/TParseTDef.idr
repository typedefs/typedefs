module TParse

import Data.Vect

import TParsec
import TParsec.Running
import TParsec.NEList

import Typedefs
import Types

%default total
%access public export

-- TODO included in latest TParsec
length : NEList a -> Nat
length = S . length . tail  

toVect : (nel : NEList a) -> Vect (length nel) a
toVect (MkNEList h t) = h :: fromList t

-- `Vect n (m : Nat ** P m)` decorated with chained proofs of maximality
data VMax : Nat -> Nat -> (Nat -> Type) -> Type where
  VMEnd : (x : Nat) -> (px : p x) -> VMax (S Z) x p
  VMConsLess : (x : Nat) -> (px : p x) -> VMax k y p -> LTE x y -> VMax (S k) y p
  VMConsMore : (x : Nat) -> (px : p x) -> VMax k y p -> LTE y x -> VMax (S k) x p

-- find maximum and decorate input Vect
toVMax : Vect (S k) (n ** p n) -> (m ** VMax (S k) m p)
toVMax [(x**px)] = (x ** VMEnd x px)
toVMax ((x**px)::y::ys) =
  let (m**vmax) = toVMax (y::ys) in
  case isLTE x m of
    Yes prf =>   (m ** VMConsLess x px vmax prf)
    No contra => (x ** VMConsMore x px vmax (notLTImpliesGTE $ contra . lteSuccLeft))

-- push proofs to elements
fromVMax : VMax k m p -> Vect k (n ** (LTE n m, p n))
fromVMax {m} vm = go lteRefl vm
  where
  go : LTE s m -> VMax q s p -> Vect q (r ** (LTE r m, p r))
  go lte (VMEnd s ps)             = [(s ** (lte, ps))]
  go lte (VMConsLess x px vs prf) = (x**(lteTransitive prf lte, px)) :: go lte vs
  go lte (VMConsMore s ps vs prf) = (s**(lte, ps)) :: go (lteTransitive prf lte) vs

---

-- TODO add to stdlib?
minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     m    _   = rewrite plusZeroRightNeutral (m `minus` 0) in
                            minusZeroRight m
minusPlus (S _)  Z    lte = absurd lte
minusPlus (S n) (S m) lte = rewrite sym $ plusSuccRightSucc (m `minus` n) n in
                            cong $ minusPlus n m (fromLteSucc lte)

weakenTDef : TDef n -> (m : Nat) -> LTE n m -> TDef m
weakenTDef T0             m    prf = T0
weakenTDef T1             m    prf = T1
weakenTDef (TSum xs)      m    prf =
  TSum $ assert_total $ map (\t => weakenTDef t m prf) xs
weakenTDef (TProd xs)     m    prf =
  TProd $ assert_total $ map (\t => weakenTDef t m prf) xs
weakenTDef (TVar i)       Z    prf = absurd prf
weakenTDef (TVar {n} i)  (S m) prf =
  let prf' = fromLteSucc prf in
  rewrite sym $ minusPlus n m prf' in
  rewrite plusCommutative (m `minus` n) n in
  TVar $ weakenN ((-) m n {smaller = prf'}) i
weakenTDef (TMu nm xs)    m    prf =
  TMu nm $ assert_total $ map (\(nm', td) => (nm', weakenTDef td (S m) (LTESucc prf))) xs

---

Parser' : Type -> Nat -> Type
Parser' = Parser (SizedList Char) Char Maybe

tdef : All (Parser' (n ** TDef n))
tdef = fix _ $ \rec =>
  alts [ cmap (Z ** T0) $ withSpaces (string "Void")
       , cmap (Z ** T0) $ withSpaces (string "Unit")
       , map (\((n1**x),nel) =>
               -- find the upper bound and weaken all elements to it
               let vs = (n1**x) :: (head nel) :: (Vect.fromList $ tail nel)
                   (mx**vx) = toVMax vs
                  in
               (mx ** TProd $ map (\(_**(lte,td)) => weakenTDef td mx lte) (fromVMax vx))) $
         parens (rand (withSpaces (char '*'))
                (map2 {a=Parser' _} {b=Parser' _}
                      (\p, q => and p q)
                      (map {a=Parser' _} withSpaces rec)
                      (map {a=Parser' _} (nelist . withSpaces) rec)))
       , map (\((n1**x),nel) =>
               let vs = (n1**x) :: (head nel) :: (Vect.fromList $ tail nel)
                   (mx**vx) = toVMax vs
                  in
               (mx ** TSum $ map (\(_**(lte,td)) => weakenTDef td mx lte) (fromVMax vx))) $
         parens (rand (withSpaces (char '+'))
                (map2 {a=Parser' _} {b=Parser' _}
                      (\p, q => and p q)
                      (map {a=Parser' _} withSpaces rec)
                      (map {a=Parser' _} (nelist . withSpaces) rec)))
       , map (\n => (S n ** TVar (last {n}))) $
         parens (rand (withSpaces (string "var")) (withSpaces decimalNat))
       , guardM (\(nam, nel) =>
                 -- rountrip through Vect/VMax to avoid introducing decorated List
                 let vs : Vect (length nel) (n : Nat ** (String, TDef n)) =
                       -- push names under sigma to fit in VMax
                       map (\(nam',(n**td)) => (n**(nam',td))) $ toVect nel
                     (mx**vx) = toVMax vs
                   in
                 case mx of
                   Z => Nothing
                   S m => Just (m ** TMu nam $ toList $ map (\(_**(lte,nam',td)) => (nam', weakenTDef td (S m) lte)) (fromVMax vx))
                ) $
         parens (rand (withSpaces (string "mu"))
                      (and (withSpaces alphas)
                           (map {a=Parser' _} (\t => nelist $ withSpaces $ parens $ and (withSpaces alphas) t) rec)))
       ]
