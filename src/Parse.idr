module Parse

import Data.SortedMap
import Control.Monad.State

import TParsec
import TParsec.Running
import Data.NEList

import Typedefs
import Types

import Data.Vect

%default total
%access public export

-- `Vect (S n) (m : Nat ** P m)` decorated with chained proofs of maximality
data VMax : (len : Nat) -> (max : Nat) -> (p : Nat -> Type) -> Type where
  VMEnd      : (x : Nat) -> (px : p x)                                -> VMax (S Z)   x   p
  VMConsLess : (x : Nat) -> (px : p x) -> VMax len max p -> LTE x max -> VMax (S len) max p
  VMConsMore : (x : Nat) -> (px : p x) -> VMax len max p -> LTE max x -> VMax (S len) x   p

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

PState : Type
PState = SortedMap Name (DPair Nat TDef)

MonadRun (StateT PState Identity) where
  runMonad st = pure $ evalState st empty

TPState : Type -> Type
TPState = TParsecT () Void (State PState)

sizedtok' : Type -> Parameters TPState
sizedtok' tok = MkParameters tok (SizedList tok) (const $ pure ())

Parser' : Type -> Nat -> Type
Parser' = Parser TPState (sizedtok' Char)

tdef : All (Parser' (n ** TDef n))
tdef =
   fix (Parser' (n ** TDef n)) $ \rec =>
   withSpaces $
   alts [ guardM (\(mp, nam) => lookup nam mp) $ mand (lift get) alphas
        , cmap (Z ** T0) $ string "0"
        , cmap (Z ** T1) $ string "1"
        , nary rec '*' TProd
        , nary rec '+' TSum
        , map (\n => (S n ** TVar $ last {n})) $
            parens (rand (withSpaces (string "var")) (withSpaces decimalNat))
        , randbindm
            (guardM {b=(String, (n ** TDef n))}
                    (\(nam, nel) =>
                     let vs : Vect (length nel) (n : Nat ** (String, TDef n)) =
                           -- push names under sigma to fit in VMax
                           map (\(nm,(n**td)) => (n**(nm,td))) $ toVect nel
                         (mx**vx) = toVMax vs
                       in
                     case mx of
                       Z => Nothing
                       S m => Just (nam, (m ** TMu nam $ map (\(_**(lte,nm,td)) => (nm, weakenTDef td (S m) lte))
                                                             (fromVMax vx)))
                    ) $
             parens (rand (withSpaces (string "mu"))
                          (and (withSpaces alphas)
                               (map {a=Parser' _} (\t => nelist $ withSpaces $ parens $ and (withSpaces alphas) t)
                                                  rec))))
            (\(nam, mu) => (lift $ modify $ insert nam mu) *> pure mu)
        , randbindm
            (parens (rand (withSpaces (string "name")) (and (withSpaces alphas) (map {a=Parser' _} withSpaces rec))))
            (\(nm, (n**td)) => (lift $ modify $ insert nm (n**td)) *> pure (n ** TName nm td))
        ]
 where
 nary : All (Box (Parser' (n ** TDef n))
         :-> Cst  Char
         :-> Cst ({k, m : Nat} -> Vect (2+k) (TDef m) -> TDef m)
         :->      Parser' (n ** TDef n))
 nary rec sym con =
   map (\(x,nel) =>
         -- find the upper bound and weaken all elements to it
         let (mx**vx) = toVMax (x :: toVect nel) in
         (mx ** con $ map (\(_**(lte,td)) => weakenTDef td mx lte)
                          (fromVMax vx))
       ) $
       parens (rand (withSpaces (char sym))
          (map2 {a=Parser' _} {b=Parser' _}
                (\p, q => and p q)
                (map {a=Parser' _} withSpaces rec)
                (map {a=Parser' _} (nelist . withSpaces) rec)))

||| Parse a sequence of TDefs and return the last one that parsed, accumulating
||| and substituting named entries in the process
tdefRec : All (Parser' (n ** TDef n))
tdefRec = fix _ $ \rec => map (\(a, ma) => fromMaybe a ma) $ andopt tdef rec

||| Parse a sequence of TDefs and return a non-empty list of all results,
||| accumulating and substituting named entries in the process
tdefNEL : All (Parser' (NEList (n ** TDef n)))
tdefNEL = nelist tdef

parseTDef : String -> Maybe (n : Nat ** TDef n)
parseTDef str = parseMaybe str tdefRec

parseTDefs : String -> Maybe (NEList (n : Nat ** TDef n))
parseTDefs str = parseMaybe str tdefNEL

parseThenShowTDef : String -> String
parseThenShowTDef = show . parseTDef

parseThenStrFun : String -> ((n ** TDef n) -> String) -> String
parseThenStrFun str fn = maybe ("Failed to parse '" ++ str ++ "'.") fn $ parseTDef str
