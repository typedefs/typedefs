module Typedefs.Backend.Purescript

import Data.Vect
import Data.NEList
import Data.SortedMap

import Typedefs.Names
import Typedefs.Typedefs

import        Typedefs.Backend
import        Typedefs.Backend.Data
import        Typedefs.Backend.Effects
import        Typedefs.Backend.Specialisation
import        Typedefs.Backend.Utils
import public Typedefs.Backend.Purescript.Data
import        Typedefs.Backend.Purescript.Typegen
import        Typedefs.Backend.Purescript.Termgen

import Text.PrettyPrint.WL
import Control.Monad.State

import Effects
import Effect.State
import Effect.Exception

%default total
%access export

||| Compute the list of `TNamed`s whose termdefs the termdef for the
||| given `TDef` depends on. Does not include the given `TDef` itself.
||| @ env semantic environment, used for knowing what to name things
dependencies : (env : Vect n PsType) -> TDefR n -> PurescriptLookupM (List (m ** TNamedR m))
dependencies env td =
  pure $ filter (\ (m ** t) => not $ heteroEq (def t) td)
    (nubBy (\ (m ** t), (m' ** t') => heteroEqNamed t t') !(go env td))
  where
  mutual
    -- Traverse TDef lists recursively with `go`
    traverseRec : Vect n PsType -> Vect k (TDefR n) -> PurescriptLookupM (List (m ** TNamedR m))
    traverseRec env xs = concat <$> traverseEffect (assert_total (go env)) xs

    -- Traverse TMu recursively
    goMu : Vect n PsType -> Vect k (String, TDefR (S n)) -> PurescriptLookupM (List (m ** TNamedR m))
    goMu env tds =
      let
        muType = makeType env (TMu tds)
        tdefs = map snd tds
        extendedEnv = muType :: env
       in
      traverseRec extendedEnv tdefs

    -- We return a TNamed here, because we still have access to the name information
    go : Vect n PsType -> TDefR n -> PurescriptLookupM (List (m ** TNamedR m))
    go     env    T0                             = pure []
    go     env    T1                             = pure []
    go     env   (TSum xs)                       = traverseRec env xs
    go     env   (TProd xs)                      = traverseRec env xs
    go     env   (TVar v)                        = pure []
    go {n} env t@(TMu tds)                       = pure $ (n ** TName (nameMu tds) t) :: !(goMu env tds)
    -- FRefs are not followed through the dependencies of the type they point to.
    go     env   (RRef _)                        = pure []
    go     env   (TApp {k} t@(TName name td) xs) = do
        let envxs = map (makeType env) xs
        -- dependencies of the actual td
        depTd <- case td of
                 TMu tds => goMu envxs tds -- skip the TMu itself
                 _       => go envxs td
        xs' <- traverseRec env xs
        pure $ depTd ++ [(k**t)] ++ xs' ++ (concatMap fixup xs)
      where
         -- function to fix up some unwanted entries
        fixup : {l : Nat} -> TDefR l -> List (m ** TNamedR m)
        fixup (TApp f xs) = [] -- will be counted later
        fixup (TVar i)    = [] -- will be a parameter anyway
        fixup {l} x       = [(l ** TName "" x)]

||| Given a TDef `td` and a Purescript term t of type [[ td ]] (where
||| [[ td ]] is the interpretation of td as a type), constructs a
||| Purescript Term of type `Builder`.
||| @ td TDef to build term for
||| @ t Purescript term of the TDef type the encoder should be applied to
encode : (td : TDefR n) -> (t : PsTerm) -> PurescriptTermGen n PsTerm
encode    T0            t = pure (psAbsurd t)
encode    T1            t = pure psEmpty
encode   (TSum td)      t =
  do summands <- injectionInv td
     pure $ PsCase t (map (\ (lhs, i, rhs) => (lhs, PsConcat [word i, rhs])) summands)
  where
    injectionInv : Vect (2 + k) (TDefR n) -> PurescriptTermGen n (List (PsTerm, Int, PsTerm))
    injectionInv [a, b] =
      do [freshPV] <- freshVars 1 "z"
         a' <- encode a freshPV
         b' <- encode b freshPV
         pure [ (psLeft freshPV, 0, a')
              , (psRight freshPV, 1, b')
              ]
    injectionInv (a::b::c::tds) =
      do [freshPV] <- freshVars 1 "z"
         a' <- encode a freshPV
         rest <- injectionInv (b::c::tds)
         pure $ (psLeft freshPV, 0, a') ::
                (map (\ (lhs, i, rhs) => (psRight lhs, i + 1, rhs)) rest)
encode   (TProd {k} td) t =
  do freshPVs <- freshVars (2 + k) "y"
     factors <- traverseWithIndex (\ i, t' => assert_total $ encode (index i td) t') freshPVs
     pure $ PsCase t [(PsTupC freshPVs, PsConcat (toList factors))]
encode   (TVar i)       t =
     pure $ PsApp (index i !envTerms) [t]
encode t@(TMu tds)      y =
     pure $ PsApp !(encoderTerm t) [y] -- assumes the def of eTerm is generated elsewhere
encode t@(TApp f xs)    y =
     pure $ PsApp !(encoderTerm t) [y] -- assumes the def of eTerm is generated elsewhere
encode   (RRef i)       t =
     pure $ PsApp (index i !envTerms) [t]

||| Given a TDef t, gives a Purescript term of type Deserialiser [[ t ]]
||| where [[ t ]] is the interpretation of t as a type
decode : TDefR n -> PurescriptTermGen n PsTerm
decode    T0            = pure psFailDecode
decode    T1            = pure $ psPure PsUnitTT
decode   (TSum {k} tds) =
  do cases <- traverseWithIndex f tds
     [i] <- freshVars 1 "i"
     pure $ PsDo [ (Just i, psReadInt (fromNat k))
                 , (Nothing, psCaseDef i (toList cases) psFailDecode)
                 ]
  where
    injection : Fin l -> PsTerm -> PsTerm
    injection                FZ     x = psLeft x
    injection {l = S (S Z)} (FS FZ) x = psRight x
    injection               (FS i)  x = psRight (injection i x)
    f : Fin (2 + k) -> TDefR n -> PurescriptTermGen n (PsTerm, PsTerm)
    f i t =
      do t' <- assert_total $ decode t
         [y] <- freshVars 1 "y" -- TODO: could share this name between the branches
         pure (PsInt (finToInteger i), PsDo [(Just y, t'), (Nothing, psPure (injection i y))])
decode   (TProd {k} xs) =
  do vs <- freshVars (2 + k) "x"
     xs' <- traverseWithIndex (traverseIndexDecode vs) xs
     pure (PsDo $ (toList xs') ++ [(Nothing, psPure (PsTupC vs))])
  where
    traverseIndexDecode : Vect (2 + k) PsTerm -> Fin (2 + k) -> TDefR n -> PurescriptTermGen n (Maybe PsTerm, PsTerm)
    traverseIndexDecode vars i tdef = pure (Just $ index i vars, !(assert_total $ decode tdef))
decode   (TVar i)       = pure $ index i !envTerms
decode t@(TMu tds)      = decoderTerm t -- assumes the def of this is generated elsewhere
decode t@(TApp f xs)    = decoderTerm t -- assumes the def of this is generated elsewhere
decode   (RRef i)       = pure $ index i !envTerms

||| Generate an encoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
encodeDef : TNamedR n -> PurescriptLookupM Purescript
encodeDef {n} t@(TName tname td) =
  let
    env = freshEnvWithTerms "encode"
    envTypes = map fst env
    funName = if tname == ""
                then encodeName $ makeType envTypes td
                else "encode" ++ uppercase tname
    varEncs = toList $ getUsedVars (map snd env) td
    currTerm = PsApp (PsFun funName) varEncs
    currType = if tname == ""
                 then makeType envTypes td
                 else PsParam tname []
    init = makeType' envTypes t
    funType = foldr PsArrow (psSerialiser init) (map psSerialiser (getUsedVars envTypes td))
   in
  do clauses <- toPurescriptLookupM $ genClauses n currType currTerm env varEncs td
     pure $ FunDef funName funType clauses
  where
    genConstructor : (n : Nat) -> String -> TDefR n -> PurescriptTermGen n (PsTerm, List PsTerm)
    genConstructor n name (TProd {k = k} xs) =
      do xs' <- freshVars (2 + k) "x"
         rhs <- traverseWithIndex (\ i, t' => encode (index i xs) t') xs'
         pure $ (PsInn name (toList xs'), toList rhs)
    genConstructor n name td =
      do [x'] <- freshVars 1 "x"
         rhs <- encode td x'
         pure $ (PsInn name [x'], [rhs])

    genClause : (n : Nat) -> List PsTerm -> Fin k -> (String, TDefR n) -> PurescriptTermGen n (List PsTerm, PsTerm)
    genClause n varEncs i (name, T1  ) = pure (varEncs ++ [PsInn name []], word (fromInteger (finToInteger i)))
    genClause n varEncs i (name, args) =
      do (con, rhs) <- genConstructor n name args
         pure (varEncs ++ [con], simplify $ PsConcat (word (fromInteger (finToInteger i))::rhs))

        -- Idris is not clever enough to figure out the following type if written as a case expression
    genClauses : (n : Nat) -> PsType -> PsTerm -> Vect n (PsType, PsTerm) -> List PsTerm -> TDefR n -> Either CompilerError (List (List PsTerm, PsTerm))
    genClauses n currType currTerm env varEncs (TMu [(name, td)]) =
      -- We run this in its own `TermGen` because the state is indexed over `S n` and not `n`.
      -- Once we have the result as a value we convert it back to a `TermGen n`.
      map (\(con, rhs) => [(varEncs ++ [con], simplify $ PsConcat rhs)])
          (runTermGen ((currType, currTerm) :: env) $ genConstructor (S n) name td)

    genClauses n currType currTerm env varEncs (TMu tds) =
      map toList
          (runTermGen ((currType, currTerm) :: env) $ traverseWithIndex (genClause (S n) varEncs) tds)
    genClauses n currType currTerm env varEncs td        =
      let v = PsTermVar "x" in
      map (\encoded => [(varEncs ++ [v] , simplify encoded)])
          (runTermGen env $ encode td v)

||| Generate an decoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
decodeDef : TNamedR n -> PurescriptLookupM Purescript
decodeDef {n} t@(TName tname td) =
  let
    env = freshEnvWithTerms "decode"
    envTypes = map fst env
    funName = if tname == ""
                then decodeName $ makeType envTypes td
                else "decode" ++ uppercase tname
    varEncs = toList $ getUsedVars (map snd env) td
    currTerm = PsApp (PsFun funName) varEncs
    currType = if tname == ""
                 then makeType envTypes td
                 else PsParam tname []
    init = makeType' envTypes t
    funType = foldr PsArrow (psDeserialiser init) (map psDeserialiser (getUsedVars envTypes td))
   in
  do rhs <- genCase n currType currTerm env td
     pure $ FunDef funName funType [(varEncs, rhs)]
  where
    genConstructor : (n : Nat) -> String -> TDefR n -> PurescriptTermGen n (List (PsTerm, PsTerm))
    genConstructor n name (TProd {k = k} xs) =
      do vs <- freshVars (2 + k) "x"
         xs' <- traverseWithIndex (\ i, x => pure (index i vs, !(decode x))) xs
         pure $ toList xs'
    genConstructor n name td =
      do [v] <- freshVars 1 "x"
         xs' <- decode td
         pure $ [(v, xs')]

    genCases : (n : Nat) -> Fin k -> (String, TDefR n) -> PurescriptTermGen n (PsTerm, PsTerm)
    genCases n i (name, T1  ) = pure (PsInt (finToInteger i), psPure (PsInn name []))
    genCases n i (name, args) =
      do args' <- genConstructor n name args
         pure (PsInt (finToInteger i), PsDo $ (map (\ (x, e) => (Just x, e)) args')++[(Nothing, psPure (PsInn name (map fst args')))])

    -- Idris is not clever enough to figure out the following type if written as a case expression
    genCase : (n : Nat) -> PsType -> PsTerm -> Vect n (PsType, PsTerm) -> TDefR n -> PurescriptLookupM PsTerm
    genCase n currType currTerm env (TMu [(name, td)]) =
      toPurescriptLookupM $ map (simplify . snd) $ runTermGen ((currType, currTerm)::env) (genCases {k = S Z} (S n) FZ (name, td))
    genCase n currType currTerm env (TMu {k} tds)      =
      toPurescriptLookupM $ runTermGen ((currType, currTerm)::env) (
        do cases <- traverseWithIndex (genCases (S n)) tds
           [i] <- freshVars 1 "i"
           pure $ PsDo [ (Just i, psReadInt (fromNat k))
                       , (Nothing, simplify $ psCaseDef i (toList cases) psFailDecode)
                       ])
    genCase n currType currTerm env td = toPurescriptLookupM $ map simplify $ runTermGen env (decode td)

ASTGen Purescript PsType True where
  msgType  (Unbounded tn) = pure $ makeType' freshEnv tn
  generateTyDefs declaredSpecialisations tns =
    runMakeDefM {t=(PsType, PsTerm)} $ do
      let specialisedMap = specialisedTypes {t=(PsType, PsTerm)}
      'Names :- put declaredSpecialisations
      concat <$> traverseEffect (\(Unbounded tn) => makeDefs' tn) (toVect tns)
  generateTermDefs tns = runMakeDefM $
    do gen <- traverseEffect genPurescript (toVect tns)
       pure $ concat gen
    where
      genTerms : TNamedR n -> PurescriptLookupM (List Purescript)
      genTerms tn = pure [!(encodeDef tn), !(decodeDef tn)]

      generateNext : TNamedR n -> PurescriptDefM (List Purescript)
      generateNext tn = ifNotPresent (name tn) (genTerms tn)

      genPurescript : ZeroOrUnbounded TNamedR True -> PurescriptDefM (List Purescript)
      genPurescript (Unbounded {n} tn) =
        do deps <- (dependencies freshEnv (def tn))
           let genFrom = deps ++ [(n ** tn)]
           concat <$> traverseEffect (\(n ** tn) => generateNext tn) (fromList genFrom)

CodegenIndep Purescript PsType where
  typeSource = renderType
  defSource  = renderDef
  preamble   = text """module Typedefs.Definitions

import Data.Void (Void, absurd)
import Data.Maybe (Just(..), Nothing)
import Data.Tuple.Nested (type (/\), (/\))

import Data.ByteString
import Data.ByteString.Encode

type Serialiser a = a -> Builder

runSerialiser :: Serialiser a -> a -> ByteString
runSerialiser f = toLazyByteString . f

newtype Deserialiser a = MkDeserialiser (ByteString -> Maybe (a /\ ByteString))

runDeserialiser :: Deserialiser a -> ByteString -> Maybe (a /\ ByteString)
runDeserialiser (MkDeserialiser f) = f

instance functorD :: Functor Deserialiser where
  fmap f da = MkDeserialiser (\ bs -> do
    (a /\ bs') <- runDeserialiser da bs
    Just (f a /\ bs'))

instance applicativeD :: Applicative Deserialiser where
  pure x = MkDeserialiser (\ bs -> Just (x /\ bs))
  df <*> da =  MkDeserialiser (\ bs -> do
    (f /\ bs') <- runDeserialiser df bs
    (a /\ bs'') <- runDeserialiser da bs'
    Just (f a /\ bs''))

instance monadD :: Monad Deserialiser where
  da >>= g = MkDeserialiser (\ bs -> do
    (a /\ bs') <- runDeserialiser da bs
    runDeserialiser (g a) bs')

failDecode :: Deserialiser a
failDecode = MkDeserialiser (\ bs -> Nothing)

deserialiseInt :: Deserialiser Integer
deserialiseInt = MkDeserialiser (\ bs -> map go (uncons bs))
  where go :: (Word8 /\ ByteString) -> (Integer /\ ByteString)
        go (b /\ bs') = (toInteger b /\ bs')"""
