module Typedefs.Backend.Haskell.Termgen

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
import Typedefs.Backend.Haskell.Data
import Typedefs.Backend.Haskell.Typegen

import Text.PrettyPrint.WL

import Effects
import Effect.State
import Effect.Exception

private
hsParam : Decl -> HsType
hsParam (MkDecl n ps) = HsParam n (map HsVar ps)

specialisedMap : SortedMap String (HsType, HsTerm)
specialisedMap = foldr {t=List} (uncurry insert) empty $
                 [ ("Int"  , (hsNamed "Int"  , HsUnitTT))
                 , ("Bool" , (hsNamed "Bool" , HsUnitTT))
                 , ("Maybe", (hsNamed "Maybe", HsUnitTT))
                 , ("List" , (hsNamed "List" , HsUnitTT))
                 ]

export
Specialisation (HsType, HsTerm) where
  specialisedTypes = specialisedMap

-- Effects -----

public export
HaskellTermGen : Nat -> Type -> Type
HaskellTermGen = TermGen (HsType, HsTerm)

export
traverseWithIndex : (Fin n -> a -> HaskellTermGen m b) -> Vect n a -> HaskellTermGen m (Vect n b)
traverseWithIndex f []        = pure []
traverseWithIndex f (x :: xs) = do y <- f FZ x
                                   ys <- traverseWithIndex (f . FS) xs
                                   pure (y :: ys)

public export
HaskellDefM : Type -> Type
HaskellDefM = MakeDefM (HsType, HsTerm)

-- The state monad in which name lookup happens, contains a sorted map of existing types, can throw errors
public export
HaskellLookupM : Type -> Type
HaskellLookupM = LookupM (HsType, HsTerm)

export
toHaskellLookupM : Either CompilerError a -> HaskellLookupM a
toHaskellLookupM (Left err) = raise err
toHaskellLookupM (Right val) = pure val

-- Execute the lookup monad, any error will result in a `Left` value.
export
runHaskellLookupM : HaskellLookupM a -> Either CompilerError a
runHaskellLookupM = runLookupM

subEffect :  (Eff a es -> Either CompilerError a) -> Eff a es -> HaskellTermGen n a
subEffect run eff= toTermGen $ run eff

-- Rendering Haskell source code -----

mutual
  ||| Render a term as Haskell source code.
  renderTerm : HsTerm -> Doc
  renderTerm  HsUnitTT         = text "()"
  renderTerm (HsTupC xs)       = hsTupled . toList . map (assert_total guardParenTerm) $ xs
  renderTerm (HsTermVar x)     = text x
  renderTerm  HsWildcard       = text "_"
  renderTerm (HsInn name [])   = text name
  renderTerm (HsInn name args) = text name |++| hsep (toList $ map (assert_total guardParenTerm) $ args)
  renderTerm (HsCase t bs)     = align $ text "case" |++| align (renderTerm t) |++| text "of" |+| breakLine
      |+| indent 2 (vsep (toList (map (hang 2 . (assert_total $ renderCase)) bs)))
  renderTerm (HsApp f [])      = renderTerm f
  renderTerm (HsApp f xs)      = renderTerm f |++| hsep (toList $ map (assert_total guardParenTerm) $ xs)
  renderTerm (HsFun f)         = text f
  renderTerm (HsDo exprs)      =
    align $ text "do" |+| breakLine
     |+| indent 2 (vsep (map (hang 2 . (assert_total $ renderDoExp)) exprs))
  renderTerm (HsWord8 i)       = text "fromIntegral" |++| text (show i)
  renderTerm (HsInt i)         = text (show i)
  renderTerm (HsConcat xs)     = text "mconcat" |++| (list . map (assert_total guardParenTerm) $ xs)

  ||| As `renderTerm`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParenTerm : HsTerm -> Doc
  guardParenTerm t@(HsInn _ (a::as)) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsCase _ _)      = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsApp _ [])      = assert_total $ renderTerm t
  guardParenTerm t@(HsApp _ _)       = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsWord8 _)       = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsConcat _)      = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsDo _)          = parens (assert_total $ renderTerm t)
  guardParenTerm t                   = assert_total $ renderTerm t

  -- helper functions

  private
  renderCase : (HsTerm, HsTerm) -> Doc
  renderCase (lhs, rhs) = renderTerm lhs |++| text "->" |++| (renderTerm rhs)

  private
  renderDoExp : (Maybe HsTerm, HsTerm) -> Doc
  renderDoExp (Nothing, e) = renderTerm e
  renderDoExp (Just x , e) = renderTerm x |++| text "<-" |++| renderTerm e

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

||| Render a type definition as Haskell source code.
export
renderDef : Haskell -> Doc
renderDef (Synonym decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
renderDef (ADT     decl cases) = text "data" |++| renderDecl decl
                                 |++| equals |++| hsep (punctuate (text " |")
                                                       (toList $ map renderConstructor cases))
  where
    renderConstructor : (Name, HsType) -> Doc
    renderConstructor (name, HsUnit)     = renderApp name []
    renderConstructor (name, HsTuple ts) = renderApp name (map guardParen ts)
    renderConstructor (name, params)     = renderApp name [guardParen params]
renderDef (FunDef name type clauses) = vsep $ (text name |++| text "::" |++| renderType type)
                                                ::(toList $ map renderClause clauses)
  where
    renderClause : (List HsTerm, HsTerm) -> Doc
    renderClause ([]  , rhs) = text name |++| equals |++| renderTerm rhs
    renderClause (args, rhs) = text name |++| (hsep (toList $ map guardParenTerm args)) |++| equals |++| renderTerm rhs

-- Simplifying Haskell source code -----

||| The variable names occurring freely in the term
freeVars : HsTerm -> List Name
freeVars    HsUnitTT           = []
freeVars   (HsTupC xs)         = nub $ concatMap (assert_total freeVars) xs
freeVars   (HsTermVar y)       = [y]
freeVars    HsWildcard         = []
freeVars   (HsInn c xs)        = nub $ concatMap (assert_total freeVars) xs
freeVars   (HsCase t xs)       =
  (nub $ (freeVars t) ++ (concatMap (assert_total $ freeVars . snd) xs)) \\
  (concatMap (assert_total $ freeVars . fst) xs)
freeVars   (HsApp f xs)        = nub $ (freeVars f) ++ (concatMap (assert_total freeVars) xs)
freeVars   (HsFun f)           = []
freeVars   (HsDo [])           = []
freeVars t@(HsDo ((p, e)::xs)) =
   let pvars = maybe [] (assert_total freeVars) p
       evars = freeVars e
       rest = freeVars (assert_smaller t (HsDo xs))
   in (nub $ (evars ++ rest)) \\ pvars
freeVars   (HsWord8 i)         = []
freeVars   (HsInt i)           = []
freeVars   (HsConcat xs)       = nub $ concatMap (assert_total $ freeVars) xs

||| Substitute `a` for `HsTermVar x` in `t`
substHS : HsTerm -> String -> HsTerm -> HsTerm
substHS a x  HsUnitTT     = HsUnitTT
substHS a x (HsTupC xs)   = HsTupC (map (assert_total $ substHS a x) xs)
substHS a x (HsTermVar y) = if x == y then a else HsTermVar y
substHS a x  HsWildcard   = HsWildcard
substHS a x (HsInn c xs)  = HsInn c (map (assert_total $ substHS a x) xs)
substHS a x (HsCase t xs) = HsCase (substHS a x t) (map (assert_total captureAvoid) xs)
  where
    captureAvoid : (HsTerm, HsTerm) -> (HsTerm, HsTerm)
    captureAvoid (p, e) =
      let pvars = freeVars p in
      if x `elem` pvars then (p, e) else (p, substHS a x e)
      -- TODO: do properly: if freeVars a `intersect` pvars is not
       -- empty, rename clashing variables in p and e before substituting
substHS a x (HsApp f xs)  = HsApp (substHS a x f) (map (assert_total $ substHS a x) xs)
substHS a x (HsFun f)     = HsFun f
substHS a x (HsDo xs)     = HsDo (assert_total $ captureAvoid xs)
  where
    captureAvoid : List (Maybe HsTerm, HsTerm) -> List (Maybe HsTerm, HsTerm)
    captureAvoid []             = []
    captureAvoid s@((p, e)::xs) =
      let pvars = maybe [] freeVars p in
      if x `elem` pvars then s
                        else (p, substHS a x e)::(captureAvoid xs)
      -- TODO: do properly; as above, but must avoid clashes also in xs
substHS a x (HsWord8 i)   = HsWord8 i
substHS a x (HsInt i)     = HsInt i
substHS a x (HsConcat xs) = HsConcat (map (assert_total $ substHS a x) xs)

||| Simplify haskell terms:
||| - In do blocks: `(return a) >>= f` ~> f a
||| - mconcat [] ~> mempty
||| - mconcat [a] ~> a
||| - mconcat (xs ++ [mempty] ++ ys) ~> mconcat (xs ++ ys)
export
simplify : HsTerm -> HsTerm
simplify (HsDo xs) =
  let xs' = simpDo xs in
  case xs' of
    [(Nothing, e)] => assert_total $ simplify e
    _ => HsDo xs'
  where
    simpDo : List (Maybe HsTerm, HsTerm) -> List (Maybe HsTerm, HsTerm)
    simpDo []           = []
    simpDo ((p, e)::xs) =
      let e' = simplify e in
      case (p, e') of
        -- replace "x <- return a; e" by "e[a/x]"
        -- assumes the free variables in a are not bound in e
        (Just (HsTermVar x), HsApp (HsFun "return") [a]) =>
           assert_total $ simpDo (map (\ (q, f) => (q, substHS a x f)) xs)
        _ => (p, e')::(simpDo xs)
simplify (HsCase t cases) = HsCase (simplify t) (map (\ (p,e) => (p, assert_total $ simplify e)) cases)
simplify (HsApp f xs)     = HsApp (simplify f) (map (assert_total simplify) xs)
simplify  HsUnitTT        = HsUnitTT
simplify (HsTupC xs)      = HsTupC (map (assert_total simplify) xs)
simplify (HsTermVar i)    = HsTermVar i
simplify  HsWildcard      = HsWildcard
simplify (HsInn c xs)     = HsInn c (map (assert_total simplify) xs)
simplify (HsFun f)        = HsFun f
simplify (HsWord8 i)      = HsWord8 i
simplify (HsInt i)        = HsInt i
simplify (HsConcat xs)    =
  let xs' = filter notMempty (map (assert_total simplify) xs) in
  case xs' of
    []  => HsFun "mempty"
    [a] => a
    _   => HsConcat xs'
  where
    notMempty : HsTerm -> Bool
    notMempty (HsFun "mempty") = False
    notMempty _                = True

-- Generate type definitions -----

-- Fresh "semantic" environments

||| A fresh environment of "semantic" types
export
freshEnv : Vect n HsType
-- Haskell type variables start with lowercase letters.
freshEnv = map (either HsVar hsParam) $ freshEnv "x"

private
hsTypeName : HsType -> Name
hsTypeName  HsVoid        = "Void"
hsTypeName  HsUnit        = "Unit"
hsTypeName (HsTuple xs)   = "Prod" ++ (concatMap (assert_total hsTypeName) xs)
hsTypeName (HsSum a b)    = "Sum" ++ hsTypeName a ++ hsTypeName b
hsTypeName (HsVar v)      = v
hsTypeName (HsParam n xs) = n --  ++ (concatMap (assert_total hsTypeName) xs)
hsTypeName (HsArrow a b)  = "Arrow" ++ hsTypeName a ++ hsTypeName b

||| A fresh environment of "semantic" types and decoder/encoder term
||| variables, with a given prefix.
||| @ prefix string to use before term variable names
export
freshEnvWithTerms : (prefix : String) -> Vect n (HsType, HsTerm)
freshEnvWithTerms prefix = map (\ x => (x, HsTermVar (prefix ++ uppercase (hsTypeName x)))) freshEnv


mutual
  ||| Generate all the Haskell type definitions that a `TDef` depends on.
  makeDefs : TDefR n -> HaskellDefM (List Haskell)
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
  makeTypeFromCase : Vect n HsType -> (String, TDefR n) -> HaskellDefM (String, HsType)
  makeTypeFromCase env (name, def) = pure (name, makeType env def)

  ||| Generate Haskell type definitions for a `TNamed` and all of its dependencies.
  export
  makeDefs' : TNamedR n -> HaskellDefM (List Haskell)
  makeDefs' (TName name body) = ifNotPresent name $ addName name body

  addName : Name -> TDefR n -> HaskellDefM (List Haskell)
  addName name body =
      let freshEnvString = map (\ x => case x of HsVar v => v; _ => "") freshEnv
          decl           = MkDecl name (getUsedVars freshEnvString body) in
      case body of
        -- Named `TMu`s are treated as ADTs.
        TMu cases => do let newEnv = hsParam decl :: freshEnv
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
hsAbsurd : HsTerm -> HsTerm
hsAbsurd t = HsApp (HsFun "absurd") [t]

-- `mempty :: Builder` from Data.ByteString.Builder
export
hsEmpty : HsTerm
hsEmpty = HsFun "mempty"

-- `Deserialiser` type family
export
hsDeserialiser : HsType -> HsType
hsDeserialiser a = HsParam "Deserialiser" [a]

-- `Serialiser` type family
export
hsSerialiser : HsType -> HsType
hsSerialiser a = HsParam "Serialiser" [a]

-- `deserialiseInt :: Deserialiser Integer`
-- @k how many bits should be read (currently ignored)
export
hsReadInt : Integer -> HsTerm
hsReadInt k = HsApp (HsFun "deserialiseInt") [] -- [HsInt k]

-- `failDecode :: Deserialiser a`
export
hsFailDecode : HsTerm
hsFailDecode = HsFun "failDecode"

-- `return :: a -> Deserialiser a`
export
hsReturn : HsTerm -> HsTerm
hsReturn x = HsApp (HsFun "return") [x]

-- `Left : a -> Either a b`
export
hsLeft : HsTerm -> HsTerm
hsLeft x = HsInn "Left" [x]

-- `Right : b -> Either a b`
export
hsRight : HsTerm -> HsTerm
hsRight x = HsInn "Right" [x]

-- `case t of cases; _ -> def`
export
hsCaseDef : HsTerm -> List (HsTerm, HsTerm) -> HsTerm -> HsTerm
hsCaseDef t cases def = HsCase t (cases ++ [(HsWildcard, def)])

-- `word8 :: Word8 -> Builder` from Data.ByteString.Builder
export
word : Int -> HsTerm
word i = HsApp (HsFun "word8") [HsWord8 i]


||| Given an environment, run the term generator, with no names
||| already used to start with.
|||| @ env environment to use

||| Extract an environment of types.
envTypes : HaskellTermGen n (Vect n HsType)
envTypes = do (_, fs) <- 'Env :- get
              pure $ map fst fs

||| Extract an environment of encoder/decoder terms.
export
envTerms : HaskellTermGen n (Vect n HsTerm)
envTerms = do (_, fs) <- 'Env :- get
              pure $ map snd fs

||| Generate a vector of fresh variables, using a given string as a
||| name suggestion.
||| @ k number of variables to generate
||| @ suggestion name to use if possible
export
freshVars : (k : Nat) -> (suggestion : String) -> HaskellTermGen n (Vect k HsTerm)
freshVars Z suggestion = pure []
freshVars k@(S n) suggestion =
  do (alreadyUsed, fs) <- 'Env :- get
     let currentCount = maybe 0 id (SortedMap.lookup suggestion alreadyUsed)
     let newUsed = insert suggestion (fromNat $ (toNat currentCount) + k) (delete suggestion alreadyUsed)
     'Env :- put (newUsed, fs)
     pure $ map (\ i => HsTermVar $ suggestion ++ (showVar $ currentCount + (toNat i))) range
 where
   -- We want x, x0, x1, ...
   showVar : Nat -> String
   showVar Z = ""
   showVar (S n) = show n

||| Name to use for encoder at this type.
export
encodeName : HsType -> Name
encodeName ty = "encode" ++ (uppercase $ hsTypeName ty)

||| Name to use for decoder at this type.
export
decodeName : HsType -> Name
decodeName ty = "decode" ++ (uppercase $ hsTypeName ty)

||| Term to use for encoder/decoder for the given `TDef`.
||| @ namer should be either `encodeName` or `decodeName`; determines if
|||         we generate the encoder or decoder term.
encoderDecoderTerm : (namer : HsType -> Name) -> TDefR n -> HaskellTermGen n HsTerm
encoderDecoderTerm namer (TApp g xs) =
  do xs' <- traverseEffect (assert_total $ encoderDecoderTerm namer) xs
     pure (HsApp (HsFun (namer (HsParam (name g) []))) (toList xs'))
encoderDecoderTerm namer (TVar i)    = index i <$> envTerms
encoderDecoderTerm namer td          =
  do env <- envTerms
     let varEncoders = getUsedVars env td
     let rawType = makeType freshEnv td
     pure $ HsApp (HsFun (namer rawType)) (toList varEncoders)

||| Term to use for encoder for this `TDef`.
export
encoderTerm : TDefR n -> HaskellTermGen n HsTerm
encoderTerm td = encoderDecoderTerm encodeName td

||| Term to use for encoder for this `TDef`.
export
decoderTerm : TDefR n -> HaskellTermGen n HsTerm
decoderTerm td = encoderDecoderTerm decodeName td
