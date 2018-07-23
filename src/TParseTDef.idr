module TParse

import Data.Vect

import TParsec
import TParsec.Running
import TParsec.NEList

import Typedefs
import Types

%default total
%access public export

data VMax : Nat -> Nat -> (Nat -> Type) -> Type where
  VMEnd : (x : Nat) -> (px : p x) -> VMax (S Z) x p
  VMConsLess : (x : Nat) -> (px : p x) -> VMax k y p -> LTE x y -> VMax (S k) y p
  VMConsMore : (x : Nat) -> (px : p x) -> VMax k y p -> LTE y x -> VMax (S k) x p

toVMax : Vect (S k) (n ** p n) -> (m ** VMax (S k) m p)
toVMax [(x**px)] = (x ** VMEnd x px)
toVMax ((x**px)::y::ys) = let (m**vmax) = toVMax (y::ys) in 
                           case isLTE x m of 
                             Yes prf =>   (m ** VMConsLess x px vmax prf)
                             No contra => (x ** VMConsMore x px vmax (notLTImpliesGTE $ contra . lteSuccLeft))  

fromVMax : VMax k m p -> Vect k (n ** (LTE n m, p n))
fromVMax {m} vm = go lteRefl vm
  where
  go : LTE s m -> VMax q s p -> Vect q (r ** (LTE r m, p r))
  go lte (VMEnd s ps)             = [(s ** (lte, ps))]
  go lte (VMConsLess x px vs prf) = (x**(lteTransitive prf lte, px)) :: go lte vs
  go lte (VMConsMore s ps vs prf) = (s**(lte, ps)) :: go (lteTransitive prf lte) vs                             

---

minusPlus : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
minusPlus  Z     Z    lte = Refl
minusPlus (S _)  Z    lte = absurd lte
minusPlus  Z    (S m) lte = cong $ plusZeroRightNeutral m
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
tdef = fix (Parser' (n ** TDef n)) $ \rec => 
  alts [ cmap (Z ** T0) $ withSpaces (string "Void")
       , cmap (Z ** T0) $ withSpaces (string "Unit")
       , map (\((n1**x),nel) => 
               let vs = (n1**x) :: (head nel) :: (Vect.fromList $ tail nel)
                   (mx**vx) = toVMax vs
                   vs' = fromVMax vx
                  in 
               (mx ** TProd $ map (\(n**(lte,td)) => weakenTDef td mx lte) vs')) $ 
         parens (rand (withSpaces (char '*')) 
                (map2 {a=Parser' _} {b=Parser' _} 
                      (\p, q => and p q) 
                      rec 
                      (map {a=Parser' _} nelist rec)))
       , map (\((n1**x),nel) => 
               let vs = (n1**x) :: (head nel) :: (Vect.fromList $ tail nel)
                   (mx**vx) = toVMax vs
                   vs' = fromVMax vx
                  in 
               (mx ** TSum $ map (\(n**(lte,td)) => weakenTDef td mx lte) vs')) $ 
         parens (rand (withSpaces (char '+')) 
                (map2 {a=Parser' _} {b=Parser' _} 
                      (\p, q => and p q) 
                      rec 
                      (map {a=Parser' _} nelist rec)))
       ]
