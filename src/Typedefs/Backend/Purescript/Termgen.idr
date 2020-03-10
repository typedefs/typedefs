module Typedefs.Backend.Purescript.Termgen

import Data.Vect
import Data.NEList
import Data.SortedMap

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.Backend
import Typedefs.Backend.Data
import Typedefs.Backend.Effects
import Typedefs.Backend.Specialisation
import Typedefs.Backend.Utils
import Typedefs.Backend.Purescript.Data
import Typedefs.Backend.Purescript.Typegen

import Text.PrettyPrint.WL

import Effects
import Effect.State
import Effect.Exception

private
psParam : Decl -> PsType
psParam (MkDecl n ps) = PsParam n (map PsVar ps)

specialisedMap : SortedMap String (PsType, PsTerm)
specialisedMap = foldr {t=List} (uncurry insert) empty $
                 [ ("Int"  , (psNamed "Int"  , PsUnitTT))
                 , ("Bool" , (psNamed "Bool" , PsUnitTT))
                 , ("Maybe", (psNamed "Maybe", PsUnitTT))
                 , ("List" , (psNamed "List" , PsUnitTT))
                 ]

export
Specialisation (PsType, PsTerm) where
  specialisedTypes = specialisedMap

-- Effects -----

public export
PurescriptTermGen : Nat -> Type -> Type
PurescriptTermGen = TermGen (PsType, PsTerm)

export
traverseWithIndex : (Fin n -> a -> PurescriptTermGen m b) -> Vect n a -> PurescriptTermGen m (Vect n b)
traverseWithIndex f []        = pure []
traverseWithIndex f (x :: xs) = do y <- f FZ x
                                   ys <- traverseWithIndex (f . FS) xs
                                   pure (y :: ys)

public export
PurescriptDefM : Type -> Type
PurescriptDefM = MakeDefM (PsType, PsTerm)

-- The state monad in which name lookup happens, contains a sorted map of existing types, can throw errors
public export
PurescriptLookupM : Type -> Type
PurescriptLookupM = LookupM (PsType, PsTerm)

export
toPurescriptLookupM : Either CompilerError a -> PurescriptLookupM a
toPurescriptLookupM (Left err) = raise err
toPurescriptLookupM (Right val) = pure val

-- Execute the lookup monad, any error will result in a `Left` value.
export
runPurescriptLookupM : PurescriptLookupM a -> Either CompilerError a
runPurescriptLookupM = runLookupM

subEffect :  (Eff a es -> Either CompilerError a) -> Eff a es -> PurescriptTermGen n a
subEffect run eff= toTermGen $ run eff

-- Rendering Purescript source code -----

mutual
  ||| Render a term as Purescript source code.
  renderTerm : PsTerm -> Doc
  renderTerm  PsUnitTT         = text "()"
  renderTerm (PsTupC xs)       = psTupled . toList . map (assert_total guardParenTerm) $ xs
  renderTerm (PsTermVar x)     = text x
  renderTerm  PsWildcard       = text "_"
  renderTerm (PsInn name [])   = text name
  renderTerm (PsInn name args) = text name |++| hsep (toList $ map (assert_total guardParenTerm) $ args)
  renderTerm (PsCase t bs)     = align $ text "case" |++| align (renderTerm t) |++| text "of" |+| breakLine
      |+| indent 2 (vsep (toList (map (hang 2 . (assert_total $ renderCase)) bs)))
  renderTerm (PsApp f [])      = renderTerm f
  renderTerm (PsApp f xs)      = renderTerm f |++| hsep (toList $ map (assert_total guardParenTerm) $ xs)
  renderTerm (PsFun f)         = text f
  renderTerm (PsDo exprs)      =
    align $ text "do" |+| breakLine
     |+| indent 2 (vsep (map (hang 2 . (assert_total $ renderDoExp)) exprs))
  renderTerm (PsWord8 i)       = text "fromIntegral" |++| text (show i)
  renderTerm (PsInt i)         = text (show i)
  renderTerm (PsConcat xs)     = text "mconcat" |++| (list . map (assert_total guardParenTerm) $ xs)

  ||| As `renderTerm`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParenTerm : PsTerm -> Doc
  guardParenTerm t@(PsInn _ (a::as)) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(PsCase _ _)      = parens (assert_total $ renderTerm t)
  guardParenTerm t@(PsApp _ [])      = assert_total $ renderTerm t
  guardParenTerm t@(PsApp _ _)       = parens (assert_total $ renderTerm t)
  guardParenTerm t@(PsWord8 _)       = parens (assert_total $ renderTerm t)
  guardParenTerm t@(PsConcat _)      = parens (assert_total $ renderTerm t)
  guardParenTerm t@(PsDo _)          = parens (assert_total $ renderTerm t)
  guardParenTerm t                   = assert_total $ renderTerm t

  -- helper functions

  private
  renderCase : (PsTerm, PsTerm) -> Doc
  renderCase (lhs, rhs) = renderTerm lhs |++| text "->" |++| (renderTerm rhs)

  private
  renderDoExp : (Maybe PsTerm, PsTerm) -> Doc
  renderDoExp (Nothing, e) = renderTerm e
  renderDoExp (Just x , e) = renderTerm x |++| text "<-" |++| renderTerm e

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

||| Render a type definition as Purescript source code.
export
renderDef : Purescript -> Doc
renderDef (Synonym decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
renderDef (ADT     decl cases) = text "data" |++| renderDecl decl
                                 |++| equals |++| hsep (punctuate (text " |")
                                                       (toList $ map renderConstructor cases))
  where
    renderConstructor : (Name, PsType) -> Doc
    renderConstructor (name, PsUnit)     = renderApp name []
    renderConstructor (name, PsTuple ts) = renderApp name (map guardParen ts)
    renderConstructor (name, params)     = renderApp name [guardParen params]
renderDef (FunDef name type clauses) = vsep $ (text name |++| text "::" |++| renderType type)
                                                ::(toList $ map renderClause clauses)
  where
    renderClause : (List PsTerm, PsTerm) -> Doc
    renderClause ([]  , rhs) = text name |++| equals |++| renderTerm rhs
    renderClause (args, rhs) = text name |++| (hsep (toList $ map guardParenTerm args)) |++| equals |++| renderTerm rhs

-- Simplifying Purescript source code -----

||| The variable names occurring freely in the term
freeVars : PsTerm -> List Name
freeVars    PsUnitTT           = []
freeVars   (PsTupC xs)         = nub $ concatMap (assert_total freeVars) xs
freeVars   (PsTermVar y)       = [y]
freeVars    PsWildcard         = []
freeVars   (PsInn c xs)        = nub $ concatMap (assert_total freeVars) xs
freeVars   (PsCase t xs)       =
  (nub $ (freeVars t) ++ (concatMap (assert_total $ freeVars . snd) xs)) \\
  (concatMap (assert_total $ freeVars . fst) xs)
freeVars   (PsApp f xs)        = nub $ (freeVars f) ++ (concatMap (assert_total freeVars) xs)
freeVars   (PsFun f)           = []
freeVars   (PsDo [])           = []
freeVars t@(PsDo ((p, e)::xs)) =
   let pvars = maybe [] (assert_total freeVars) p
       evars = freeVars e
       rest = freeVars (assert_smaller t (PsDo xs))
   in (nub $ (evars ++ rest)) \\ pvars
freeVars   (PsWord8 i)         = []
freeVars   (PsInt i)           = []
freeVars   (PsConcat xs)       = nub $ concatMap (assert_total $ freeVars) xs

||| Substitute `a` for `PsTermVar x` in `t`
substHS : PsTerm -> String -> PsTerm -> PsTerm
substHS a x  PsUnitTT     = PsUnitTT
substHS a x (PsTupC xs)   = PsTupC (map (assert_total $ substHS a x) xs)
substHS a x (PsTermVar y) = if x == y then a else PsTermVar y
substHS a x  PsWildcard   = PsWildcard
substHS a x (PsInn c xs)  = PsInn c (map (assert_total $ substHS a x) xs)
substHS a x (PsCase t xs) = PsCase (substHS a x t) (map (assert_total captureAvoid) xs)
  where
    captureAvoid : (PsTerm, PsTerm) -> (PsTerm, PsTerm)
    captureAvoid (p, e) =
      let pvars = freeVars p in
      if x `elem` pvars then (p, e) else (p, substHS a x e)
      -- TODO: do properly: if freeVars a `intersect` pvars is not
       -- empty, rename clashing variables in p and e before substituting
substHS a x (PsApp f xs)  = PsApp (substHS a x f) (map (assert_total $ substHS a x) xs)
substHS a x (PsFun f)     = PsFun f
substHS a x (PsDo xs)     = PsDo (assert_total $ captureAvoid xs)
  where
    captureAvoid : List (Maybe PsTerm, PsTerm) -> List (Maybe PsTerm, PsTerm)
    captureAvoid []             = []
    captureAvoid s@((p, e)::xs) =
      let pvars = maybe [] freeVars p in
      if x `elem` pvars then s
                        else (p, substHS a x e)::(captureAvoid xs)
      -- TODO: do properly; as above, but must avoid clashes also in xs
substHS a x (PsWord8 i)   = PsWord8 i
substHS a x (PsInt i)     = PsInt i
substHS a x (PsConcat xs) = PsConcat (map (assert_total $ substHS a x) xs)

||| Simplify Purescript terms:
||| - In do blocks: `(return a) >>= f` ~> f a
||| - mconcat [] ~> mempty
||| - mconcat [a] ~> a
||| - mconcat (xs ++ [mempty] ++ ys) ~> mconcat (xs ++ ys)
export
simplify : PsTerm -> PsTerm
simplify (PsDo xs) =
  let xs' = simpDo xs in
  case xs' of
    [(Nothing, e)] => assert_total $ simplify e
    _ => PsDo xs'
  where
    simpDo : List (Maybe PsTerm, PsTerm) -> List (Maybe PsTerm, PsTerm)
    simpDo []           = []
    simpDo ((p, e)::xs) =
      let e' = simplify e in
      case (p, e') of
        -- replace "x <- return a; e" by "e[a/x]"
        -- assumes the free variables in a are not bound in e
        (Just (PsTermVar x), PsApp (PsFun "return") [a]) =>
           assert_total $ simpDo (map (\ (q, f) => (q, substHS a x f)) xs)
        _ => (p, e')::(simpDo xs)
simplify (PsCase t cases) = PsCase (simplify t) (map (\ (p,e) => (p, assert_total $ simplify e)) cases)
simplify (PsApp f xs)     = PsApp (simplify f) (map (assert_total simplify) xs)
simplify  PsUnitTT        = PsUnitTT
simplify (PsTupC xs)      = PsTupC (map (assert_total simplify) xs)
simplify (PsTermVar i)    = PsTermVar i
simplify  PsWildcard      = PsWildcard
simplify (PsInn c xs)     = PsInn c (map (assert_total simplify) xs)
simplify (PsFun f)        = PsFun f
simplify (PsWord8 i)      = PsWord8 i
simplify (PsInt i)        = PsInt i
simplify (PsConcat xs)    =
  let xs' = filter notMempty (map (assert_total simplify) xs) in
  case xs' of
    []  => PsFun "mempty"
    [a] => a
    _   => PsConcat xs'
  where
    notMempty : PsTerm -> Bool
    notMempty (PsFun "mempty") = False
    notMempty _                = True

-- Generate type definitions -----

-- Fresh "semantic" environments

||| A fresh environment of "semantic" types
export
freshEnv : Vect n PsType
-- Purescript type variables start with lowercase letters.
freshEnv = map (either PsVar psParam) $ freshEnv "x"

private
psTypeName : PsType -> Name
psTypeName  PsVoid        = "Void"
psTypeName  PsUnit        = "Unit"
psTypeName (PsTuple xs)   = "Prod" ++ (concatMap (assert_total psTypeName) xs)
psTypeName (PsSum a b)    = "Sum" ++ psTypeName a ++ psTypeName b
psTypeName (PsVar v)      = v
psTypeName (PsParam n xs) = n --  ++ (concatMap (assert_total psTypeName) xs)
psTypeName (PsArrow a b)  = "Arrow" ++ psTypeName a ++ psTypeName b

||| A fresh environment of "semantic" types and decoder/encoder term
||| variables, with a given prefix.
||| @ prefix string to use before term variable names
export
freshEnvWithTerms : (prefix : String) -> Vect n (PsType, PsTerm)
freshEnvWithTerms prefix = map (\ x => (x, PsTermVar (prefix ++ uppercase (psTypeName x)))) freshEnv


mutual
  ||| Generate all the Purescript type definitions that a `TDef` depends on.
  makeDefs : TDefR n -> PurescriptDefM (List Purescript)
  makeDefs    T0          = pure []
  makeDefs    T1          = pure []
  makeDefs    (TProd xs)  = concat <$> traverseEffect (assert_total makeDefs) xs
  makeDefs    (TSum xs)   = concat <$> traverseEffect (assert_total makeDefs) xs
  makeDefs    (TVar v)    = pure []
  makeDefs td@(TMu cases) = makeDefs' $ TName (nameMu cases) td -- We name anonymous mus using their constructors.
  makeDefs    (RRef _)    = pure []
  makeDefs    (TApp f xs) =
    do res <- assert_total $ makeDefs' f
       res' <- concat <$> traverseEffect (assert_total makeDefs) xs
       pure (res ++ res')

  -- This is only to help readabilty and type inference
  makeTypeFromCase : Vect n PsType -> (String, TDefR n) -> PurescriptDefM (String, PsType)
  makeTypeFromCase env (name, def) = pure (name, makeType env def)

  ||| Generate Purescript type definitions for a `TNamed` and all of its dependencies.
  export
  makeDefs' : TNamedR n -> PurescriptDefM (List Purescript)
  makeDefs' (TName name body) = ifNotPresent name $ addName name body

  addName : Name -> TDefR n -> PurescriptDefM (List Purescript)
  addName name body =
      let freshEnvString = map (\ x => case x of PsVar v => v; _ => "") freshEnv
          decl           = MkDecl name (getUsedVars freshEnvString body) in
      case body of
        -- Named `TMu`s are treated as ADTs.
        TMu cases => do let newEnv = psParam decl :: freshEnv
                        args <- traverseEffect (makeTypeFromCase newEnv) cases
                        res <- traverseEffect (\(_, body) => assert_total $ makeDefs body) cases
                        pure $ (concat res) ++ [ADT decl args]
        -- All other named types are treated as synonyms.
        _ => do res <- assert_total $ makeDefs body
                let type = makeType freshEnv body
                pure $ res ++ [Synonym decl type]

-- Convenience definitions for Termdefs -----

-- `absurd :: Void -> a` from Data.Void
export
psAbsurd : PsTerm -> PsTerm
psAbsurd t = PsApp (PsFun "absurd") [t]

-- `mempty :: Builder` from Data.ByteString.Builder
export
psEmpty : PsTerm
psEmpty = PsFun "mempty"

-- `Deserialiser` type family
export
psDeserialiser : PsType -> PsType
psDeserialiser a = PsParam "Deserialiser" [a]

-- `Serialiser` type family
export
psSerialiser : PsType -> PsType
psSerialiser a = PsParam "Serialiser" [a]

-- `deserialiseInt :: Deserialiser Integer`
-- @k how many bits should be read (currently ignored)
export
psReadInt : Integer -> PsTerm
psReadInt k = PsApp (PsFun "deserialiseInt") [] -- [PsInt k]

-- `failDecode :: Deserialiser a`
export
psFailDecode : PsTerm
psFailDecode = PsFun "failDecode"

-- `pure :: a -> Deserialiser a`
export
psPure : PsTerm -> PsTerm
psPure x = PsApp (PsFun "pure") [x]

-- `Left : a -> Either a b`
export
psLeft : PsTerm -> PsTerm
psLeft x = PsInn "Left" [x]

-- `Right : b -> Either a b`
export
psRight : PsTerm -> PsTerm
psRight x = PsInn "Right" [x]

-- `case t of cases; _ -> def`
export
psCaseDef : PsTerm -> List (PsTerm, PsTerm) -> PsTerm -> PsTerm
psCaseDef t cases def = PsCase t (cases ++ [(PsWildcard, def)])

-- `word8 :: Word8 -> Builder` from Data.ByteString.Builder
export
word : Int -> PsTerm
word i = PsApp (PsFun "word8") [PsWord8 i]


||| Given an environment, run the term generator, with no names
||| already used to start with.
|||| @ env environment to use

||| Extract an environment of types.
envTypes : PurescriptTermGen n (Vect n PsType)
envTypes = do (_, fs) <- 'Env :- get
              pure $ map fst fs

||| Extract an environment of encoder/decoder terms.
export
envTerms : PurescriptTermGen n (Vect n PsTerm)
envTerms = do (_, fs) <- 'Env :- get
              pure $ map snd fs

||| Generate a vector of fresh variables, using a given string as a
||| name suggestion.
||| @ k number of variables to generate
||| @ suggestion name to use if possible
export
freshVars : (k : Nat) -> (suggestion : String) -> PurescriptTermGen n (Vect k PsTerm)
freshVars Z suggestion = pure []
freshVars k@(S n) suggestion =
  do (alreadyUsed, fs) <- 'Env :- get
     let currentCount = maybe 0 id (SortedMap.lookup suggestion alreadyUsed)
     let newUsed = insert suggestion (fromNat $ (toNat currentCount) + k) (delete suggestion alreadyUsed)
     'Env :- put (newUsed, fs)
     pure $ map (\ i => PsTermVar $ suggestion ++ (showVar $ currentCount + (toNat i))) range
 where
   -- We want x, x0, x1, ...
   showVar : Nat -> String
   showVar Z = ""
   showVar (S n) = show n

||| Name to use for encoder at this type.
export
encodeName : PsType -> Name
encodeName ty = "encode" ++ (uppercase $ psTypeName ty)

||| Name to use for decoder at this type.
export
decodeName : PsType -> Name
decodeName ty = "decode" ++ (uppercase $ psTypeName ty)

||| Term to use for encoder/decoder for the given `TDef`.
||| @ namer should be either `encodeName` or `decodeName`; determines if
|||         we generate the encoder or decoder term.
encoderDecoderTerm : (namer : PsType -> Name) -> TDefR n -> PurescriptTermGen n PsTerm
encoderDecoderTerm namer (TApp g xs) =
  do xs' <- traverseEffect (assert_total $ encoderDecoderTerm namer) xs
     pure (PsApp (PsFun (namer (PsParam (name g) []))) (toList xs'))
encoderDecoderTerm namer (TVar i)    = index i <$> envTerms
encoderDecoderTerm namer td          =
  do env <- envTerms
     let varEncoders = getUsedVars env td
     let rawType = makeType freshEnv td
     pure $ PsApp (PsFun (namer rawType)) (toList varEncoders)

||| Term to use for encoder for this `TDef`.
export
encoderTerm : TDefR n -> PurescriptTermGen n PsTerm
encoderTerm td = encoderDecoderTerm encodeName td

||| Term to use for encoder for this `TDef`.
export
decoderTerm : TDefR n -> PurescriptTermGen n PsTerm
decoderTerm td = encoderDecoderTerm decodeName td
