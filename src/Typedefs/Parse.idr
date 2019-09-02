module Typedefs.Parse

import Data.SortedMap
import Data.NEList
import Control.Monad.State

import TParsec
import TParsec.Running

import Typedefs.Typedefs
import Typedefs.Names

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

PState : Type
PState = SortedMap Name (n ** TDef n)

Pointed (SortedMap Name a) where
  point = empty

data Error : Type where
  ParseError : Position -> Error
  RunError : Error

Show Error where
  show (ParseError p) = "parse error: " ++ show p
  show RunError = "internal error"

Eq Error where
  (ParseError e1) == (ParseError e2) = e1 == e2
  RunError        == RunError        = True
  _               == _               = False

Subset (Position, List Void) Error where
  into = ParseError . fst

TPState : Type -> Type
TPState = TParsecT Error Void (State PState)

Parser' : Type -> Nat -> Type
Parser' = Parser TPState chars

getResult : Result Error (Maybe a) -> Result Error a
getResult res = res >>= (Result.fromMaybe RunError)

resultToEither : Result Error a -> Either String a
resultToEither = result (Left . show) (Left . show) Right

comment : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
           All (Parser mn p ())
comment = cmap () $ and (char ';') (roptand (nelist $ anyCharBut '\n') (char '\n'))

spacesOrComments : (Alternative mn, Monad mn, Subset Char (Tok p), Inspect (Toks p) (Tok p), Eq (Tok p)) =>
                   All (Parser mn p ())
spacesOrComments {p} = cmap () $ nelist $ comment `alt` (cmap () $ spaces {p})

ignoreSpaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
               All (Parser mn p a :-> Parser mn p a)
ignoreSpaces parser = spacesOrComments `roptand` (parser `landopt` spacesOrComments)

-- main parser

tApp : {m,k : Nat} -> TNamed k -> Vect m (TDef n) -> Maybe (TDef n)
tApp {m} {k} f xs with (decEq k m)
  | Yes p = Just $ TApp f (rewrite p in xs)
  | No _  = Nothing

pushName : Name -> (n ** TDef n) -> (n ** TNamed n)
pushName name (n**td) = (n ** TName name td)

tdefRef : All (Parser' (n ** TDef n))
tdefRef = guardM
            (\(mp, nam) => pure (Z ** !(tApp (snd $ pushName nam !(lookup nam mp)) [])))
            (mand (lift get) alphas)

tdefName : All (Box (Parser' (n ** TDef n)) :-> Parser' (n ** TDef n))
tdefName rec = guardM
  {a=((m**TNamed m), NEList (n**TDef n))}
  (\(f,xs) =>
      let (mx**vx) = toVMax (toVect xs)
       in pure (mx ** !(tApp (snd f) $ map (\(_**(lte,td)) => weakenTDef td mx lte) (fromVMax vx)))
  )
  (parens (and (guardM (\(mp, nam) => pushName nam <$> lookup nam mp) $ mand (lift get) alphas)
               (Nat.map {a=Parser' _} (nelist . ignoreSpaces) rec)))

tdefNary : All (Box (Parser' (n ** TDef n))
        :-> Cst  Char
        :-> Cst ({k, m : Nat} -> Vect (2+k) (TDef m) -> TDef m)
        :->      Parser' (n ** TDef n))
tdefNary rec sym con =
  map (\(x,nel) =>
        -- find the upper bound and weaken all elements to it
        let (mx**vx) = toVMax (x :: toVect nel) in
        (mx ** con $ map (\(_**(lte,td)) => weakenTDef td mx lte)
                         (fromVMax vx))
      ) $
      parens (rand (ignoreSpaces (char sym))
         (map2 {a=Parser' _} {b=Parser' _}
               (\p, q => commit $ and p q)
               (map {a=Parser' _} (ignoreSpaces . commit) rec)
               (map {a=Parser' _} (commit . nelist . ignoreSpaces) rec)))

tdefVar : All (Parser' (n ** TDef n))
tdefVar = map {b=(n ** TDef n)} (\n => (S n ** TVar $ last {n})) $
            parens $ rand (ignoreSpaces $ string "var") (ignoreSpaces $ commit $ decimalNat)

tdefMu : All (Box (Parser' (n ** TDef n)) :-> Parser' (n ** TDef n))
tdefMu rec = Combinators.map {a=NEList (String, (n : Nat ** TDef n))}
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
                (Nat.map {a=Parser' _} (\t => commit $ nelist $ ignoreSpaces $ parens $ and (ignoreSpaces alphas) t) rec)))

tdefZero : All (Parser' (n ** TDef n))
tdefZero = cmap (the (n ** TDef n) (Z ** T0)) $ char '0'

tdefOne : All (Parser' (n ** TDef n))
tdefOne = cmap (the (n ** TDef n) (Z ** T1)) $ char '1'

tdef : All (Parser' (n ** TDef n))
tdef =
   fix (Parser' (n ** TDef n)) $ \rec =>
   ignoreSpaces $
   alts [ tdefRef
        , tdefName rec
        , tdefZero
        , tdefOne
        , tdefNary rec '*' TProd
        , tdefNary rec '+' TSum
        , tdefVar
        , tdefMu rec
        ]

tnamed : All (Parser' (n ** TNamed n))
tnamed =
  ignoreSpaces $
  randbindm
    (parens $ rand (ignoreSpaces $ string "name")
                   (and (ignoreSpaces alphas) (ignoreSpaces tdef)))
    (\(nm, (n**td)) => (lift $ modify $ insert nm (n**td)) *> pure (n ** TName nm td))

||| Parse a sequence of TDefs and return the last one that parsed, accumulating
||| and substituting named entries in the process
tdefRec : All (Parser' (n ** TDef n))
tdefRec = fix _ $ \rec => map (\(a, ma) => fromMaybe a ma) $ andopt tdef rec

||| Parse a sequence of TDefs and return a non-empty list of all results,
||| accumulating and substituting named entries in the process
tdefNEL : All (Parser' (NEList (n ** TDef n)))
tdefNEL = nelist tdef

parseTDef : String -> Result Error (n : Nat ** TDef n)
parseTDef str = getResult $ parseResult str tdefRec

parseTDefs : String -> Result Error (NEList (n : Nat ** TDef n))
parseTDefs str = getResult $ parseResult str tdefNEL

parseThenShowTDef : String -> String
parseThenShowTDef = show . parseTDef

parseTDefThenStrFun : String -> ((n ** TDef n) -> String) -> String
parseTDefThenStrFun str fn = result show show fn $ parseTDef str

||| Parse a sequence of `TNamed`s and return the last one that parsed, accumulating
||| and substituting named entries in the process.
tnamedRec : All (Parser' (n ** TNamed n))
tnamedRec = fix _ $ \rec => map (\(a, ma) => fromMaybe a ma) $ andopt tnamed rec

||| Parse a sequence of `TNamed`s and return a non-empty list of all results,
||| accumulating and substituting named entries in the process.
tnamedNEL : All (Parser' (NEList (n ** TNamed n)))
tnamedNEL = nelist tnamed

parseTNamed : String -> Result Error (n : Nat ** TNamed n)
parseTNamed str = getResult $ parseResult str tnamedRec

parseTNameds : String -> Result Error (NEList (n : Nat ** TNamed n))
parseTNameds str = getResult $ parseResult str tnamedNEL

parseThenShowTNamed : String -> String
parseThenShowTNamed = show . parseTNamed

parseTNamedThenStrFun : String -> ((n ** TNamed n) -> String) -> String
parseTNamedThenStrFun str fn = result show show fn $ parseTNamed str

specializedList : All (Parser' (NEList String))
specializedList = nelist $ parens $ rand (ignoreSpaces $ string "specialized") (ignoreSpaces $ alphas)

topLevel : All (Parser' TopLevelDef)
topLevel = withSpecialized `alt` withoutSpecialized
  where
    withoutSpecialized : All (Parser' TopLevelDef)
    withoutSpecialized = map (MkTopLevelDef []) tnamedNEL

    withSpecialized : All (Parser' TopLevelDef)
    withSpecialized = map (\(s, t) => MkTopLevelDef (Data.NEList.toList s) t) $ and specializedList tnamedNEL

parseTopLevel : String -> Result Error TopLevelDef
parseTopLevel str = getResult $ parseResult str topLevel
