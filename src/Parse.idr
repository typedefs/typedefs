module Parse

import Data.SortedMap
import Control.Monad.State

import TParsec
import TParsec.Running
import Data.NEList

import Typedefs
import Names

import Data.Vect

import ParserUtils

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

neComments : (Alternative mn, Monad mn, Subset Char (Tok p), Inspect (Toks p) (Tok p), Eq (Tok p)) =>
             All (Parser mn p ())
neComments = between (char ';') (char '\n') (cmap () $ nelist $ notChar '\n')

emptyComments : (Alternative mn, Monad mn, Subset Char (Tok p), Inspect (Toks p) (Tok p), Eq (Tok p)) =>
                All (Parser mn p ())
emptyComments = cmap () $ string ";\n"

comments : (Alternative mn, Monad mn, Subset Char (Tok p), Inspect (Toks p) (Tok p), Eq (Tok p)) =>
           All (Parser mn p (NEList ()))
comments = nelist $ emptyComments `alt` neComments

spacesOrComment : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
                 All (Parser mn p ())
spacesOrComment = (cmap () spaces) `alt` (cmap () comments)

ignoreSpaces : (Alternative mn, Monad mn,  Subset Char (Tok p),  Eq (Tok p), Inspect (Toks p) (Tok p)) =>
               All (Parser mn p a :-> Parser mn p a)
ignoreSpaces parser = roptand (nelist spacesOrComment) (landopt parser (nelist spacesOrComment))

tdef : All (Parser' (n ** TDef n))
tdef =
   fix (Parser' (n ** TDef n)) $ \rec =>
   ignoreSpaces $
   alts [ guardM
              (\(mp, nam) => pure (Z ** !(tApp (snd $ pushName nam !(lookup nam mp)) [])))
              (mand (lift get) alphas)
        , guardM
              {a=((m**TNamed m), NEList (n**TDef n))}
              (\(f,xs) => 
                  let (mx**vx) = toVMax (toVect xs)
                   in pure (mx ** !(tApp (snd f) $ map (\(_**(lte,td)) => weakenTDef td mx lte) (fromVMax vx)))
              )
              (parens (and (guardM (\(mp, nam) => pushName nam <$> lookup nam mp) $ mand (lift get) alphas)
                           (map {a=Parser' _} (nelist . ignoreSpaces) rec)))
        , cmap (Z ** T0) $ string "0"
        , cmap (Z ** T1) $ string "1"
        , nary rec '*' TProd
        , nary rec '+' TSum
        , map (\n => (S n ** TVar $ last {n})) $
            parens (rand (ignoreSpaces (string "var")) (ignoreSpaces decimalNat))
        , map {a=NEList (String, (n : Nat ** TDef n))}
              (\nel =>
               let vs : Vect (length nel) (n : Nat ** (String, TDef n)) =
                     -- push names under sigma to fit in VMax
                     map (\(nm,(n**td)) => (n**(nm,td))) $ toVect nel
                   (mx**vx) = toVMax vs
                 in
               case mx of
                 Z => (Z ** TMu $ map (\(_**(lte,nm,td)) => (nm, weakenTDef td (S Z) (lteSuccRight lte))) (fromVMax vx))
                 S m => (m ** TMu $ map (\(_**(lte,nm,td)) => (nm, weakenTDef td (S m) lte)) (fromVMax vx))
              )
              (parens (rand (ignoreSpaces (string "mu"))
                            (map {a=Parser' _} (\t => nelist $ ignoreSpaces $ parens $ and (ignoreSpaces alphas) t) rec)))
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
        parens (rand (ignoreSpaces (char sym))
           (map2 {a=Parser' _} {b=Parser' _}
                 (\p, q => and p q)
                 (map {a=Parser' _} ignoreSpaces rec)
                 (map {a=Parser' _} (nelist . ignoreSpaces) rec)))
 
  tApp : {m,k : Nat} -> TNamed k -> Vect m (TDef n) -> Maybe (TDef n)
  tApp {m} {k} f xs with (decEq k m)
    | Yes p = Just $ TApp f (rewrite p in xs)
    | No _  = Nothing

  pushName : Name -> (n ** TDef n) -> (n ** TNamed n)
  pushName name (n**td) = (n ** TName name td)

tnamed : All (Parser' (n ** TNamed n))
tnamed =
  ignoreSpaces $
  randbindm
    (parens (rand (ignoreSpaces (string "name")) (and (ignoreSpaces alphas) (ignoreSpaces tdef))))
    (\(nm, (n**td)) => (lift $ modify $ insert nm (n**td)) *> pure (n ** TName nm td))

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

parseTDefThenStrFun : String -> ((n ** TDef n) -> String) -> String
parseTDefThenStrFun str fn = maybe ("Failed to parse '" ++ str ++ "'.") fn $ parseTDef str

||| Parse a sequence of `TNamed`s and return the last one that parsed, accumulating
||| and substituting named entries in the process.
tnamedRec : All (Parser' (n ** TNamed n))
tnamedRec = fix _ $ \rec => map (\(a, ma) => fromMaybe a ma) $ andopt tnamed rec

||| Parse a sequence of `TNamed`s and return a non-empty list of all results,
||| accumulating and substituting named entries in the process.
tnamedNEL : All (Parser' (NEList (n ** TNamed n)))
tnamedNEL = nelist tnamed

parseTNamed : String -> Maybe (n : Nat ** TNamed n)
parseTNamed str = parseMaybe str tnamedRec

parseTNameds : String -> Maybe (NEList (n : Nat ** TNamed n))
parseTNameds str = parseMaybe str tnamedNEL

parseThenShowTNamed : String -> String
parseThenShowTNamed = show . parseTNamed

parseTNamedThenStrFun : String -> ((n ** TNamed n) -> String) -> String
parseTNamedThenStrFun str fn = maybe ("Failed to parse '" ++ str ++ "'.") fn $ parseTNamed str
