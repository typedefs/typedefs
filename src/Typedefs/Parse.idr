module Typedefs.Parse

import Data.SortedMap
import Data.NEList
import Data.Tuple
import Control.Monad.State

import TParsec
import TParsec.Running

import Typedefs.Typedefs
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

-- TODO add to tparsec
--Monoid a => Pointed a where
--  point = neutral

Pointed (SortedMap Name a, List b) where
  point = (empty, [])

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
TPState = TParsecT Error Void (State (SortedMap Name (n ** TDefR n), List (Name, Maybe Nat)))

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

tApp : {m,k : Nat} -> TNamedR k -> Vect m (TDefR n) -> Maybe (TDefR n)
tApp {m} {k} f xs with (decEq k m)
  | Yes p = Just $ TApp f (rewrite p in xs)
  | No _  = Nothing

pushName : Name -> (n ** TDefR n) -> (n ** TNamedR n)
pushName name (n**td) = (n ** TName name td)

findIndex' : Eq a => Nat -> a -> Vect n a -> Maybe (m ** Fin (S m))
findIndex' _ elem [] = Nothing
findIndex' idx elem (x :: xs) = if x == elem
                                  then Just (idx ** last {n=idx})
                                  else findIndex' (S idx) elem xs

pushRef : Name -> (names : List Name) -> Maybe (k ** TDefR k)
pushRef nm names = do (m ** fin) <- findIndex' Z nm $ fromList names
                      pure (S m ** RRef fin)

handleName : ((SortedMap Name (n ** TDefR n), List (Name, Maybe Nat)), Name) -> Maybe (n ** TDefR n)
handleName ((mp, spec), name) =
  case SortedMap.lookup name mp of
    Just found => pure (Z ** !(tApp (DPair.snd $ pushName name found) []))
    Nothing => pushRef name (map fst spec)

tdefRef : All (Parser' (n ** TDefR n))
tdefRef = guardM
            handleName
            (mand (lift get) alphas)

handleNameArgument : ((SortedMap String (k ** TDefR k), List (String, Maybe Nat)), String) -> Maybe (n ** TNamedR n)
handleNameArgument ((mp, ls), name) = maybe (do Just ix <- lookup name ls
                                                  | Nothing => Nothing --handleName ((mp, ls), name)
                                                Just $ (ix ** TName name T0)) Just
  (pushName name <$> SortedMap.lookup name mp)

tdefName : All (Box (Parser' (n ** TDefR n)) :-> Parser' (n ** TDefR n))
tdefName rec = guardM
  -- 2. and then we try to apply the list of argument to the first name
  {a=((m**TNamedR m), NEList (n**TDefR n))}
  (\(f,xs) =>
      let (mx**vx) = toVMax (toVect xs)
          args = map (\(_**(lte,td)) => weakenTDef td mx lte) (fromVMax vx)
       in do v <- tApp (snd f) args
             pure (mx ** v)
  )
  -- 1. first we parse the name and the arguments (recursively) as a list
  (parens (and (guardM handleNameArgument
                       (mand (lift get) alphas))
               (Nat.map {a=Parser' _} (nelist . ignoreSpaces) rec)))

tdefNary : All (Box (Parser' (n ** TDefR n))
        :-> Cst  Char
        :-> Cst ({k, m : Nat} -> Vect (2+k) (TDefR m) -> TDefR m)
        :->      Parser' (n ** TDefR n))
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

tdefVar : All (Parser' (n ** TDefR n))
tdefVar = map {b=(n ** TDefR n)} (\n => (S n ** TVar $ last {n})) $
            parens $ rand (ignoreSpaces $ string "var") (ignoreSpaces $ commit $ decimalNat)

tdefMu : All (Box (Parser' (n ** TDefR n)) :-> Parser' (n ** TDefR n))
tdefMu rec = Combinators.map {a=NEList (String, (n : Nat ** TDefR n))}
  (\nel =>
   let vs : Vect (length nel) (n : Nat ** (String, TDefR n)) =
         -- push names under sigma to fit in VMax
         map (\(nm,(n**td)) => (n**(nm,td))) $ toVect nel
       (mx**vx) = toVMax vs
     in
   case mx of
     Z   => (Z ** TMu $ map (\(_**(lte,nm,td)) => (nm, weakenTDef td (S Z) (lteSuccRight lte))) (fromVMax vx))
     S m => (m ** TMu $ map (\(_**(lte,nm,td)) => (nm, weakenTDef td (S m) lte)) (fromVMax vx))
  )
  (parens (rand (ignoreSpaces (string "mu"))
                (Nat.map {a=Parser' _} (\t => commit $ nelist $ ignoreSpaces $ parens $ and (ignoreSpaces alphas) t) rec)))

tdefZero : All (Parser' (n ** TDefR n))
tdefZero = cmap (the (n ** TDefR n) (Z ** T0)) $ char '0'

tdefOne : All (Parser' (n ** TDefR n))
tdefOne = cmap (the (n ** TDefR n) (Z ** T1)) $ char '1'

tdef : All (Parser' (n ** TDefR n))
tdef =
   fix (Parser' (n ** TDefR n)) $ \rec =>
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


tnamed : All (Parser' (n ** TNamedR n))
tnamed =
  ignoreSpaces $
  randbindm
    (parens $ rand (ignoreSpaces $ string "name")
                   (and (ignoreSpaces alphas) (ignoreSpaces tdef)))
    (\(nm, (n**td)) => (lift $ modify $ mapFst $ insert nm (n**td)) *> pure (n ** TName nm td))

||| Parse a sequence of TDefRs and return the last one that parsed, accumulating
||| and substituting named entries in the process
tdefRec : All (Parser' (n ** TDefR n))
tdefRec = fix _ $ \rec => map (\(a, ma) => fromMaybe a ma) $ andopt tdef rec

||| Parse a sequence of TDefRs and return a non-empty list of all results,
||| accumulating and substituting named entries in the process
tdefNEL : All (Parser' (NEList (n ** TDefR n)))
tdefNEL = nelist tdef

parseTDef : String -> Result Error (n : Nat ** TDefR n)
parseTDef str = getResult $ parseResult str tdefRec

parseTDefs : String -> Result Error (NEList (n : Nat ** TDefR n))
parseTDefs str = getResult $ parseResult str tdefNEL

parseThenShowTDef : String -> String
parseThenShowTDef = show . parseTDef

parseTDefThenStrFun : String -> ((n ** TDefR n) -> String) -> String
parseTDefThenStrFun str fn = result show show fn $ parseTDef str

||| Parse a sequence of `TNamedR`s and return the last one that parsed, accumulating
||| and substituting named entries in the process.
tnamedRec : All (Parser' (n ** TNamedR n))
tnamedRec = fix _ $ \rec => map (\(a, ma) => fromMaybe a ma) $ andopt tnamed rec

||| Parse a sequence of `TNamedR`s and return a non-empty list of all results,
||| accumulating and substituting named entries in the process.
tnamedNEL : All (Parser' (NEList (n ** TNamedR n)))
tnamedNEL = nelist tnamed

parseTNamed : String -> Result Error (n : Nat ** TNamedR n)
parseTNamed str = getResult $ parseResult str tnamedRec

parseTNameds : String -> Result Error (NEList (n : Nat ** TNamedR n))
parseTNameds str = getResult $ parseResult str tnamedNEL

parseThenShowTNamed : String -> String
parseThenShowTNamed = show . parseTNamed

parseTNamedThenStrFun : String -> ((n ** TNamedR n) -> String) -> String
parseTNamedThenStrFun str fn = result show show fn $ parseTNamed str

specialisedList : All (Parser' (NEList (String, Maybe Nat)))
specialisedList = nelist $ withSpaces spec
  where
    spec : All (Parser' (String, Maybe Nat))
    spec = parens (rand (withSpaces $ string "specialised")
                        ((withSpaces alphas) `andopt` decimalNat))

topLevel : All (Parser' TopLevelDef)
topLevel = withSpecialized `alt` withoutSpecialized
  where
    withoutSpecialized : All (Parser' TopLevelDef)
    withoutSpecialized = map (MkTopLevelDef [ ]) tnamedNEL

    ||| Given a list of specialised references, setup the initial state for the parser
    mkState : NEList a -> (SortedMap String (n : Nat ** TDef' n False), List a)
    mkState = MkPair empty . Data.NEList.toList

    ||| Parse the list of specialised references and setup the state for the rest of the parser
    parseWithSpecial : All (Parser' (NEList (String, Maybe Nat)))
    parseWithSpecial = specialisedList `landbindm` (lift . put . mkState)

    ||| First parse the specialised list and add it to the context, then parse as normal
    withSpecialized : All (Parser' TopLevelDef)
    withSpecialized = map (\(s, t) =>  MkTopLevelDef (map fst $ Data.NEList.toList s) t)
                          (parseWithSpecial `and` tnamedNEL)

parseTopLevel : String -> Result Error TopLevelDef
parseTopLevel str = getResult $ parseResult str topLevel
