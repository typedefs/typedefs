module Typedefs.Backend.Haskell

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
import public Typedefs.Backend.Haskell.Data
import        Typedefs.Backend.Haskell.Typegen
import        Typedefs.Backend.Haskell.Termgen

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
dependencies : (env : Vect n HsType) -> TDefR n -> HaskellLookupM (List (m ** TNamedR m))
dependencies env td =
  pure $ filter (\ (m ** t) => not $ heteroEq (def t) td)
    (nubBy (\ (m ** t), (m' ** t') => heteroEqNamed t t') !(go env td))
  where
  mutual
    -- Traverse TDef lists recursively with `go`
    traverseRec : Vect n HsType -> Vect k (TDefR n) -> HaskellLookupM (List (m ** TNamedR m))
    traverseRec env xs = concat <$> traverseEffect (assert_total (go env)) xs

    -- Traverse TMu recursively
    goMu : Vect n HsType -> Vect k (String, TDefR (S n)) -> HaskellLookupM (List (m ** TNamedR m))
    goMu env tds = do let muType = makeType env (TMu tds)
                      let tdefs = map snd tds
                      let extendedEnv = muType :: env
                      traverseRec extendedEnv tdefs

    -- We return a TNamed here, because we still have access to the name information
    go : Vect n HsType -> TDefR n -> HaskellLookupM (List (m ** TNamedR m))
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

||| Given a TDef `td` and a Haskell term t of type [[ td ]] (where
||| [[ td ]] is the interpretation of td as a type), constructs a
||| Haskell Term of type `Builder`.
||| @ td TDef to build term for
||| @ t Haskell term of the TDef type the encoder should be applied to
encode : (td : TDefR n) -> (t : HsTerm) -> HaskellTermGen n HsTerm
encode    T0            t = pure (hsAbsurd t)
encode    T1            t = pure hsEmpty
encode   (TSum td)      t =
  do summands <- injectionInv td
     pure $ HsCase t (map (\ (lhs, i, rhs) => (lhs, HsConcat [word i, rhs])) summands)
  where
    injectionInv : Vect (2 + k) (TDefR n) -> HaskellTermGen n (List (HsTerm, Int, HsTerm))
    injectionInv [a, b] =
      do [freshPV] <- freshVars 1 "z"
         a' <- encode a freshPV
         b' <- encode b freshPV
         pure [ (hsLeft freshPV, 0, a')
              , (hsRight freshPV, 1, b')
              ]
    injectionInv (a::b::c::tds) =
      do [freshPV] <- freshVars 1 "z"
         a' <- encode a freshPV
         rest <- injectionInv (b::c::tds)
         pure $ (hsLeft freshPV, 0, a') ::
                (map (\ (lhs, i, rhs) => (hsRight lhs, i + 1, rhs)) rest)
encode   (TProd {k} td) t =
  do freshPVs <- freshVars (2 + k) "y"
     factors <- traverseWithIndex (\ i, t' => assert_total $ encode (index i td) t') freshPVs
     pure $ HsCase t [(HsTupC freshPVs, HsConcat (toList factors))]
encode   (TVar i)       t =
     pure $ HsApp (index i !envTerms) [t]
encode t@(TMu tds)      y =
     pure $ HsApp !(encoderTerm t) [y] -- assumes the def of eTerm is generated elsewhere
encode t@(TApp f xs)    y =
     pure $ HsApp !(encoderTerm t) [y] -- assumes the def of eTerm is generated elsewhere
encode   (RRef i)       t =
     pure $ HsApp (index i !envTerms) [t]

||| Given a TDef t, gives a Haskell term of type Deserialiser [[ t ]]
||| where [[ t ]] is the interpretation of t as a type
decode : TDefR n -> HaskellTermGen n HsTerm
decode    T0            = pure hsFailDecode
decode    T1            = pure $ hsReturn HsUnitTT
decode   (TSum {k} tds) =
  do cases <- traverseWithIndex f tds
     [i] <- freshVars 1 "i"
     pure $ HsDo [ (Just i, hsReadInt (fromNat k))
                 , (Nothing, hsCaseDef i (toList cases) hsFailDecode)
                 ]
  where
    injection : Fin l -> HsTerm -> HsTerm
    injection FZ x = hsLeft x
    injection {l = S (S Z)} (FS FZ) x = hsRight x
    injection (FS i) x = hsRight (injection i x)
    f : Fin (2 + k) -> TDefR n -> HaskellTermGen n (HsTerm, HsTerm)
    f i t =
      do t' <- assert_total $ decode t
         [y] <- freshVars 1 "y" -- TODO: could share this name between the branches
         pure (HsInt (finToInteger i), HsDo [(Just y, t'), (Nothing, hsReturn (injection i y))])
decode   (TProd {k} xs) =
  do vs <- freshVars (2 + k) "x"
     xs' <- traverseWithIndex (traverseIndexDecode vs) xs
     pure (HsDo $ (toList xs') ++ [(Nothing, hsReturn (HsTupC vs))])
  where
    traverseIndexDecode : Vect (2 + k) HsTerm -> Fin (2 + k) -> TDefR n -> HaskellTermGen n (Maybe HsTerm, HsTerm)
    traverseIndexDecode vars i tdef = pure (Just $ index i vars, !(assert_total $ decode tdef))
decode   (TVar i)       = pure $ index i !envTerms
decode t@(TMu tds)      = decoderTerm t -- assumes the def of this is generated elsewhere
decode t@(TApp f xs)    = decoderTerm t -- assumes the def of this is generated elsewhere
decode   (RRef i)       = pure $ index i !envTerms

||| Generate an encoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
encodeDef : TNamedR n -> HaskellLookupM Haskell
encodeDef {n} t@(TName tname td) =
  let
    env = freshEnvWithTerms "encode"
    envTypes = map fst env
    funName = if tname == ""
                then encodeName $ makeType envTypes td
                else "encode" ++ uppercase tname
    varEncs = toList $ getUsedVars (map snd env) td
    currTerm = HsApp (HsFun funName) varEncs
    currType = if tname == ""
                 then makeType envTypes td
                 else HsParam tname []
    init = makeType' envTypes t
    funType = foldr HsArrow (hsSerialiser init) (map hsSerialiser (getUsedVars envTypes td))
   in
  do clauses <- toHaskellLookupM $ genClauses n currType currTerm env varEncs td
     pure $ FunDef funName funType clauses
  where
    genConstructor : (n : Nat) -> String -> TDefR n -> HaskellTermGen n (HsTerm, List HsTerm)
    genConstructor n name (TProd {k = k} xs) =
      do xs' <- freshVars (2 + k) "x"
         rhs <- traverseWithIndex (\ i, t' => encode (index i xs) t') xs'
         pure $ (HsInn name (toList xs'), toList rhs)
    genConstructor n name td =
      do [x'] <- freshVars 1 "x"
         rhs <- encode td x'
         pure $ (HsInn name [x'], [rhs])

    genClause : (n : Nat) -> List HsTerm -> Fin k -> (String, TDefR n) -> HaskellTermGen n (List HsTerm, HsTerm)
    genClause n varEncs i (name, T1  ) = pure (varEncs ++ [HsInn name []], word (fromInteger (finToInteger i)))
    genClause n varEncs i (name, args) =
      do (con, rhs) <- genConstructor n name args
         pure (varEncs ++ [con], simplify $ HsConcat (word (fromInteger (finToInteger i))::rhs))

        -- Idris is not clever enough to figure out the following type if written as a case expression
    genClauses : (n : Nat) -> HsType -> HsTerm -> Vect n (HsType, HsTerm) -> List HsTerm -> TDefR n -> Either CompilerError (List (List HsTerm, HsTerm))
    genClauses n currType currTerm env varEncs (TMu [(name, td)]) =
      -- We run this in its own `TermGen` because the state is indexed over `S n` and not `n`.
      -- Once we have the result as a value we convert it back to a `TermGen n`.
      map (\(con, rhs) => [(varEncs ++ [con], simplify $ HsConcat rhs)])
          (runTermGen ((currType, currTerm) :: env) $ genConstructor (S n) name td)

    genClauses n currType currTerm env varEncs (TMu tds) =
      map toList
          (runTermGen ((currType, currTerm) :: env) $ traverseWithIndex (genClause (S n) varEncs) tds)
    genClauses n currType currTerm env varEncs td        =
      let v = HsTermVar "x" in
      map (\encoded => [(varEncs ++ [v] , simplify encoded)])
          (runTermGen env $ encode td v)

||| Generate an decoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
decodeDef : TNamedR n -> HaskellLookupM Haskell
decodeDef {n} t@(TName tname td) =
  let
    env = freshEnvWithTerms "decode"
    envTypes = map fst env
    funName = if tname == ""
                then decodeName $ makeType envTypes td
                else "decode" ++ uppercase tname
    varEncs = toList $ getUsedVars (map snd env) td
    currTerm = HsApp (HsFun funName) varEncs
    currType = if tname == ""
                 then makeType envTypes td
                 else HsParam tname []
    init = makeType' envTypes t
    funType = foldr HsArrow (hsDeserialiser init) (map hsDeserialiser (getUsedVars envTypes td))
   in
  do rhs <- genCase n currType currTerm env td
     pure $ FunDef funName funType [(varEncs, rhs)]
  where
    genConstructor : (n : Nat) -> String -> TDefR n -> HaskellTermGen n (List (HsTerm, HsTerm))
    genConstructor n name (TProd {k = k} xs) =
      do vs <- freshVars (2 + k) "x"
         xs' <- traverseWithIndex (\ i, x => pure (index i vs, !(decode x))) xs
         pure $ toList xs'
    genConstructor n name td =
      do [v] <- freshVars 1 "x"
         xs' <- decode td
         pure $ [(v, xs')]

    genCases : (n : Nat) -> Fin k -> (String, TDefR n) -> HaskellTermGen n (HsTerm, HsTerm)
    genCases n i (name, T1  ) = pure (HsInt (finToInteger i), hsReturn (HsInn name []))
    genCases n i (name, args) =
      do args' <- genConstructor n name args
         pure (HsInt (finToInteger i), HsDo $ (map (\ (x, e) => (Just x, e)) args')++[(Nothing, hsReturn (HsInn name (map fst args')))])

    -- Idris is not clever enough to figure out the following type if written as a case expression
    genCase : (n : Nat) -> HsType -> HsTerm -> Vect n (HsType, HsTerm) -> TDefR n -> HaskellLookupM HsTerm
    genCase n currType currTerm env (TMu [(name, td)]) =
      toHaskellLookupM $ map (simplify . snd) $ runTermGen ((currType, currTerm)::env) (genCases {k = S Z} (S n) FZ (name, td))
    genCase n currType currTerm env (TMu {k} tds)      =
      toHaskellLookupM $ runTermGen ((currType, currTerm)::env) (
        do cases <- traverseWithIndex (genCases (S n)) tds
           [i] <- freshVars 1 "i"
           pure $ HsDo [ (Just i, hsReadInt (fromNat k))
                       , (Nothing, simplify $ hsCaseDef i (toList cases) hsFailDecode)
                       ])
    genCase n currType currTerm env td = toHaskellLookupM $ map simplify $ runTermGen env (decode td)

ASTGen Haskell HsType True where
  msgType  (Unbounded tn) = pure $ makeType' freshEnv tn
  generateTyDefs declaredSpecialisations tns =
    runMakeDefM {t=(HsType, HsTerm)} $ do
      let specialisedMap = specialisedTypes {t=(HsType, HsTerm)}
      'Names :- put declaredSpecialisations
      concat <$> traverseEffect (\(Unbounded tn) => makeDefs' tn) (toVect tns)
  generateTermDefs tns = runMakeDefM $
    do gen <- traverseEffect genHaskell (toVect tns)
       pure $ concat gen
    where
      genTerms : TNamedR n -> HaskellLookupM (List Haskell)
      genTerms tn = pure [!(encodeDef tn), !(decodeDef tn)]

      generateNext : TNamedR n -> HaskellDefM (List Haskell)
      generateNext tn = ifNotPresent (name tn) (genTerms tn)

      genHaskell : ZeroOrUnbounded TNamedR True -> HaskellDefM (List Haskell)
      genHaskell (Unbounded {n} tn) =
        do deps <- (dependencies freshEnv (def tn))
           let genFrom = deps ++ [(n ** tn)]
           concat <$> traverseEffect (\(n ** tn) => generateNext tn) (fromList genFrom)

CodegenIndep Haskell HsType where
  typeSource = renderType
  defSource  = renderDef
  preamble   = text """module Typedefs.Definitions

import Data.Word
import Data.Binary
import Data.ByteString.Lazy
import Data.ByteString.Builder

import Data.Void

type Serialiser a = a -> Builder

runSerialiser :: Serialiser a -> a -> ByteString
runSerialiser f = toLazyByteString . f

newtype Deserialiser a = MkDeserialiser (ByteString -> Maybe (a, ByteString))

runDeserialiser :: Deserialiser a -> ByteString -> Maybe (a, ByteString)
runDeserialiser (MkDeserialiser f) = f

instance Functor Deserialiser where
  fmap f da = MkDeserialiser (\ bs -> do
    (a, bs') <- runDeserialiser da bs
    Just (f a, bs'))

instance Applicative Deserialiser where
  pure x = MkDeserialiser (\ bs -> Just (x, bs))
  df <*> da =  MkDeserialiser (\ bs -> do
    (f, bs') <- runDeserialiser df bs
    (a, bs'') <- runDeserialiser da bs'
    Just (f a, bs''))

instance Monad Deserialiser where
  da >>= g = MkDeserialiser (\ bs -> do
    (a, bs') <- runDeserialiser da bs
    runDeserialiser (g a) bs')

failDecode :: Deserialiser a
failDecode = MkDeserialiser (\ bs -> Nothing)

deserialiseInt :: Deserialiser Integer
deserialiseInt = MkDeserialiser (\ bs -> fmap go (uncons bs))
  where go :: (Word8, ByteString) -> (Integer, ByteString)
        go (b, bs') = (toInteger b, bs')"""
