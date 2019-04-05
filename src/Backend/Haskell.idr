module Backend.Haskell

import Names
import Typedefs

import Backend
import Backend.Utils
import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect

%default total
%access export

||| The syntactic structure of Haskell types.
data HsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  HsVoid  :                                HsType

  ||| The `()` (i.e. unit/singleton) type.
  HsUnit  :                                HsType

  ||| The tuple type, containing two or more further types.
  HsTuple :         Vect (2 + n) HsType -> HsType

  ||| The sum type, containing two further types.
  HsSum   :         HsType -> HsType    -> HsType

  ||| A type variable.
  HsVar   :         Name                -> HsType

  ||| A named type with zero or more other types as parameters.
  HsParam : Name -> Vect n HsType       -> HsType

  ||| A function type (only used for top-level type of termdef
  ||| decoders and encoders)
  HsArrow :         HsType -> HsType    -> HsType

private
hsParam : Decl -> HsType
hsParam (MkDecl n ps) = HsParam n (map HsVar ps)

||| The syntactic structure of Haskell terms (TODO clean up)
data HsTerm : Type where
  ||| The unit term `()`
  HsUnitTT  : HsTerm

  ||| The tuple constructor, containing two or more further terms.
  HsTupC :         Vect (2 + n) HsTerm -> HsTerm

  ||| A term variable, with a name (no need for deBruijn indices when terms are first-order!)
  HsTermVar : Name -> HsTerm

  ||| The wildcard pattern `_`
  HsWildcard  : HsTerm

  ||| A data type constructor, containing a name and a list of further terms
  HsInn : Name -> List HsTerm -> HsTerm

  ||| A case expression, containing a term being examined, and a list
  ||| of (lhs, rhs) pairs. Invariants: lhs is a pattern (ie all
  ||| variables occur linearly), and FreeVars(rhs) \subseteq
  ||| FreeVars(lhs).
  HsCase : HsTerm -> List (HsTerm, HsTerm) -> HsTerm

  ||| A function application
  HsApp : HsTerm -> List HsTerm -> HsTerm

  ||| A Haskell function
  HsFun : String -> HsTerm

  ||| Do-notation: A list of statements of the form
  |||   x <- e
  ||| or simply
  |||   e
  HsDo : List (Maybe HsTerm, HsTerm) -> HsTerm

  --- constants

  ||| A Word8 converted from an Int literal
  HsWord8 : Int -> HsTerm -- fromIntegral

  ||| An Int literal
  HsInt : Integer -> HsTerm

  -- special functions

  ||| `mconcat :: [Builder] -> Builder` from Data.ByteString.Builder
  HsConcat : List HsTerm -> HsTerm

||| The syntactic structure of Haskell type declarations.
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect n (Name, HsType) -> Haskell

  ||| A function definition is a declared name, a type, and a list of
  ||| clauses of the form ((arg1, ..., argk), rhs)
  FunDef : Name -> HsType -> List (List HsTerm, HsTerm) -> Haskell

-- Haskell type variables start with lowercase letters.
-- ||| A fresh "semantic" environment
private
freshEnv : Vect n HsType
freshEnv = map (either HsVar hsParam) $ freshEnv "x"

||| Render a name applied to a list of arguments exactly as written.
||| Arguments need to be previously parenthesized, if applicable.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  ||| Render a type signature as Haskell source code.
  renderType : HsType -> Doc
  renderType HsVoid                = text "Void"
  renderType HsUnit                = text "()"
  renderType (HsTuple xs)          = tupled . toList . map (assert_total renderType) $ xs
  renderType (HsSum a b)           = renderApp "Either" [guardParen a, guardParen b]
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)
  renderType (HsArrow a b)         = (guardParen a) |++| text "->" |++| (guardParen b)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : HsType -> Doc
  guardParen t@(HsParam _ []) = assert_total $ renderType t
  guardParen t@(HsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t@(HsSum _ _ )   = parens (assert_total $ renderType t)
  guardParen t@(HsArrow _ _)  = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

mutual
  ||| Render a term as Haskell source code.
  renderTerm : HsTerm -> Doc
  renderTerm HsUnitTT         = text "()"
  renderTerm (HsTupC xs) = tupled . toList . map (assert_total guardParenTerm) $ xs
  renderTerm (HsTermVar x)    = text x
  renderTerm HsWildcard       = text "_"
  renderTerm (HsInn name []) = text name
  renderTerm (HsInn name args) = text name |++| hsep (toList $ map (assert_total guardParenTerm) $ args)
  renderTerm (HsCase t bs)  = align $ text "case" |++| align (renderTerm t) |++| text "of" |+| breakLine
      |+| indent 2
           (vsep (toList (map (hang 2 . (assert_total $ renderCase)) bs)))
    where
    renderCase : (HsTerm, HsTerm) -> Doc
    renderCase (lhs, rhs) = renderTerm lhs |++| text "->" |++| (renderTerm rhs)
  renderTerm (HsApp f [])  = renderTerm f
  renderTerm (HsApp f xs)  = renderTerm f |++| hsep (toList $ map (assert_total guardParenTerm) $ xs)
  renderTerm (HsFun f) = text f
  renderTerm (HsDo exprs) =
    align $ text "do" |+| breakLine
     |+| indent 2 (vsep (map (hang 2 . (assert_total $ renderDoExp)) exprs))
    where
    renderDoExp : (Maybe HsTerm, HsTerm) -> Doc
    renderDoExp (Nothing, e) = renderTerm e
    renderDoExp (Just x, e) = renderTerm x |++| text "<-" |++| renderTerm e
  renderTerm (HsWord8 i) = text "fromIntegral" |++| text (show i)
  renderTerm (HsInt i) = text (show i)
  renderTerm (HsConcat xs) = text "mconcat" |++| (list . map (assert_total guardParenTerm) $ xs)

  ||| As `renderTerm`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParenTerm : HsTerm -> Doc
  guardParenTerm t@(HsInn _ (a::as)) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsCase _ _) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsApp _ []) = assert_total $ renderTerm t
  guardParenTerm t@(HsApp _ _) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsWord8 _) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsConcat _) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsDo _) = parens (assert_total $ renderTerm t)
  guardParenTerm t = assert_total $ renderTerm t

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

||| Render a type definition as Haskell source code.
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
  renderClause ([], rhs) = text name |++| equals |++| renderTerm rhs
  renderClause (args, rhs) = text name |++| (hsep (map guardParenTerm args)) |++| equals |++| renderTerm rhs

private
countUp : Nat -> String -> List String -> String
countUp n x ys = let x' = x ++ show n in
  if not (x' `elem` ys) then x' else assert_total $ countUp (S n) x ys

||| The variable names occurring freely in the term
freeVars : HsTerm -> List String
freeVars HsUnitTT = []
freeVars (HsTupC xs) = nub $ concatMap (assert_total freeVars) xs
freeVars (HsTermVar y) = [y]
freeVars HsWildcard = []
freeVars (HsInn c xs) = nub $ concatMap (assert_total freeVars) xs
freeVars (HsCase t xs) = (nub $ (freeVars t) ++ (concatMap (assert_total $ freeVars . snd) xs)) \\ (concatMap (assert_total $ freeVars . fst) xs)
freeVars (HsApp f xs) = nub $ (freeVars f) ++ (concatMap (assert_total freeVars) xs)
freeVars (HsFun f) = []
freeVars (HsDo []) = []
freeVars t@(HsDo ((p, e)::xs)) =
   let pvars = maybe [] (assert_total freeVars) p
       evars = freeVars e
       rest = freeVars (assert_smaller t (HsDo xs))
   in (nub $ (evars ++ rest)) \\ pvars
freeVars (HsWord8 i) = []
freeVars (HsInt i) = []
freeVars (HsConcat xs) = nub $ concatMap (assert_total $ freeVars) xs

||| Check if `HsTermVar x` occurs freely in `t`
occurs : String -> HsTerm -> Bool
occurs x t = x `elem` freeVars t

||| Substitute `a` for `HsTermVar x` in `t`
substHS : HsTerm -> String -> HsTerm -> HsTerm
substHS a x HsUnitTT = HsUnitTT
substHS a x (HsTupC xs) = HsTupC (map (assert_total $ substHS a x) xs)
substHS a x (HsTermVar y) = if x == y then a else HsTermVar y
substHS a x HsWildcard = HsWildcard
substHS a x (HsInn c xs) = HsInn c (map (assert_total $ substHS a x) xs)
substHS a x (HsCase t xs) = HsCase (substHS a x t) (map (assert_total captureAvoid) xs)
  where captureAvoid : (HsTerm, HsTerm) -> (HsTerm, HsTerm)
        captureAvoid (p, e) = let pvars = freeVars p in
          if x `elem` pvars then (p, e) else (p, substHS a x e)
          -- TODO: do properly: if freeVars a `intersect` pvars is not
          -- empty, rename clashing variables in p and e before substituting
substHS a x (HsApp f xs) = HsApp (substHS a x f) (map (assert_total $ substHS a x) xs)
substHS a x (HsFun f) = (HsFun f)
substHS a x (HsDo xs) = HsDo (assert_total $ captureAvoid xs)
  where
  captureAvoid : List (Maybe HsTerm, HsTerm) -> List (Maybe HsTerm, HsTerm)
  captureAvoid [] = []
  captureAvoid s@((p, e)::xs) = let pvars = maybe [] freeVars p in
    if x `elem` pvars then s else (p, substHS a x e)::(captureAvoid xs)
  -- TODO: do properly; as above, but must avoid clashes also in xs
substHS a x (HsWord8 i) = HsWord8 i
substHS a x (HsInt i) = HsInt i
substHS a x (HsConcat xs) = HsConcat (map (assert_total $ substHS a x) xs)

||| Simplify haskell terms, for now only trivial bindings in do-blocks
simplify : HsTerm -> HsTerm
simplify (HsDo xs) = let xs' = simpDo xs in
  case xs' of
    [(Nothing, e)] => assert_total $ simplify e
    _ => HsDo xs'
  where
  simpDo : List (Maybe HsTerm, HsTerm) -> List (Maybe HsTerm, HsTerm)
  simpDo [] = []
  simpDo ((p, e)::xs) = let e' = simplify e in
    case (p, e') of
      -- replace "x <- return a; e" by "e[a/x]"
      -- assumes the free variables in a are not bound in e
      (Just (HsTermVar x), HsApp (HsFun "return") [a]) =>
         assert_total $ simpDo (map (\ (q, f) => (q, substHS a x f)) xs)
      _ => (p, e')::(simpDo xs)
simplify (HsCase t cases) = HsCase (simplify t) (map (\ (p,e) => (p, assert_total $ simplify e)) cases)
simplify (HsApp f xs) = HsApp (simplify f) (map (assert_total simplify) xs)
simplify HsUnitTT = HsUnitTT
simplify (HsTupC xs) = HsTupC (map (assert_total simplify) xs)
simplify (HsTermVar i) = HsTermVar i
simplify HsWildcard = HsWildcard
simplify (HsInn c xs) = HsInn c (map (assert_total simplify) xs)
simplify (HsFun f) = HsFun f
simplify (HsWord8 i) = HsWord8 i
simplify (HsInt i) = HsInt i
simplify (HsConcat xs) = let xs' = filter notMempty (map (assert_total simplify) xs) in
  case xs' of
    []  => HsFun "mempty"
    [a] => a
    _   => HsConcat xs'
  where notMempty : HsTerm -> Bool
        notMempty (HsFun "mempty") = False
        notMempty _                = True


||| Generate a Haskell type from a `TDef`.
makeType : Vect n HsType -> TDef n -> HsType
makeType _    T0          = HsVoid
makeType _    T1          = HsUnit
makeType e    (TSum xs)   = foldr1' (\t1,t2 => HsSum t1 t2) (map (assert_total $ makeType e) xs)
makeType e    (TProd xs)  = HsTuple $ map (assert_total $ makeType e) xs
makeType e    (TVar v)    = Vect.index v e
makeType e td@(TMu cases) = HsParam (nameMu cases) $ getUsedVars e td
makeType e    (TApp f xs) = HsParam (name f) (map (assert_total $ makeType e) xs)

||| Generate a Haskell type from a `TNamed`.
makeType' : Vect n HsType -> TNamed n -> HsType
makeType' e (TName "" body) = makeType e body --escape hatch
makeType' e (TName name body) = HsParam name $ getUsedVars e body

mutual
  ||| Generate all the Haskell type definitions that a `TDef` depends on.
  makeDefs : TDef n -> State (List Name) (List Haskell)
  makeDefs    T0          = pure []
  makeDefs    T1          = pure []
  makeDefs    (TProd xs)  = concat <$> traverse (assert_total makeDefs) xs
  makeDefs    (TSum xs)   = concat <$> traverse (assert_total makeDefs) xs
  makeDefs    (TVar v)    = pure []
  makeDefs td@(TMu cases) = makeDefs' $ TName (nameMu cases) td -- We name anonymous mus using their constructors.
  makeDefs    (TApp f xs) = do
      res <- assert_total $ makeDefs' f
      res' <- concat <$> traverse (assert_total makeDefs) xs
      pure (res ++ res')

  ||| Generate Haskell type definitions for a `TNamed` and all of its dependencies.
  makeDefs' : TNamed n -> State (List Name) (List Haskell)
  makeDefs' (TName name body) = ifNotPresent name $
      let freshEnvString = map (\ x => case x of HsVar v => v; _ => "") freshEnv
          decl = MkDecl name (getUsedVars freshEnvString body) in
      case body of
        TMu cases => do -- Named `TMu`s are treated as ADTs.
          let newEnv = hsParam decl :: freshEnv
          let args = map (map (makeType newEnv)) cases
          res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs bdy) (toList cases)
          pure $ ADT decl args :: res
        _ => do -- All other named types are treated as synonyms.
          res <- assert_total $ makeDefs body
          pure $ Synonym decl (makeType freshEnv body) :: res

-------- Termdefs -------------------------------------------

hsAbsurd : HsTerm -> HsTerm
hsAbsurd t = HsApp (HsFun "absurd") [t] -- `absurd :: Void -> a` from Data.Void

hsEmpty : HsTerm
hsEmpty = HsFun "mempty" -- `mempty :: Builder` from Data.ByteString.Builder

{-
||| `toLazyByteString :: Builder -> ByteString` from Data.ByteString.Builder
hstoBS : HsTerm -> HsTerm
hstoBS t = HsApp (HsFun "toLazyByteString") [t]
-}

hsByteString : HsType
hsByteString = HsParam "ByteString" []

hsDeserialiser : HsType -> HsType
hsDeserialiser a = HsParam "Deserialiser" [a]

hsSerialiser : HsType -> HsType
hsSerialiser a = HsParam "Serialiser" [a]


||| `runDeserialiser :: Deserialiser a -> ByteString -> Maybe (a, ByteString)`
hsrunDeserialiser : HsTerm -> HsTerm
hsrunDeserialiser d = HsApp (HsFun "runDeserialiser") [d]


||| `deserialiseInt :: Deserialiser Integer`; the argument
||| denotes how many bits should be read (currently ignored)
hsReadInt : Integer -> HsTerm
hsReadInt k = HsApp (HsFun "deserialiseInt") [] -- [HsInt k]

hsFailDecode : HsTerm
hsFailDecode = HsFun "failDecode"

hsReturn : HsTerm -> HsTerm
hsReturn x = HsApp (HsFun "return") [x]

private
left : HsTerm -> HsTerm
left x = HsInn "Left" [x]

private
right : HsTerm -> HsTerm
right x = HsInn "Right" [x]

hsCaseDef : HsTerm -> List (HsTerm, HsTerm) -> HsTerm -> HsTerm
hsCaseDef t cases def = HsCase t (cases ++ [(HsWildcard, def)])

infixr 10 <>
private
(<>) : HsTerm -> HsTerm -> HsTerm
a <> b = HsConcat [a, b]

private
word : Int -> HsTerm
word i = HsApp (HsFun "word8") [HsWord8 i] -- `word8 :: Word8 -> Builder` from Data.ByteString.Builder

{-
derivedName : TDef n -> Name
derivedName T0 = "Void"
derivedName T1 = "Unit"
derivedName (TSum xs) = "Sum" ++ (concatMap (assert_total derivedName) xs)
derivedName (TProd xs) = "Prod" ++ (concatMap (assert_total derivedName) xs)
derivedName (TVar v)    = "error: deriving name of type variable" -- should never happen
derivedName (TMu tds) = nameMu tds
derivedName (TApp f xs) = name f -- assert_total $ derivedName (ap (def f) xs)
-}

mapWithIndexA : Applicative m => {n : Nat} -> (Fin n -> a -> m b) -> Vect n a -> m (Vect n b)
mapWithIndexA f [] = pure []
mapWithIndexA f (a::as) = pure (::) <*> f FZ a <*> mapWithIndexA (f . FS) as

-- ||| Monad for term encoding generator, keeping track of a name
-- ||| supply and a "semantic" environment
TermEncode : Nat -> Type -> Type
TermEncode n = State (List String, Vect n (HsType,HsTerm))

runTermEncode : Vect n (HsType,HsTerm) -> TermEncode n a -> a
runTermEncode fs mx = evalState mx ([], fs)

envTypes : TermEncode n (Vect n HsType)
envTypes = do
  (_, fs) <- get
  pure $ map fst fs

envTerms : TermEncode n (Vect n HsTerm)
envTerms = do
  (_, fs) <- get
  pure $ map snd fs


freshVars : (k : Nat) -> String -> TermEncode n (Vect k HsTerm)
freshVars Z suggestion = pure []
freshVars (S n) suggestion = do
  (used, fs) <- get
  let fresh = if not (suggestion `elem` used) then suggestion
                                              else countUp 0 suggestion used
  put (fresh::used, fs)
  rest <- freshVars n suggestion
  pure $ (HsTermVar fresh) :: rest

{-
locallyExtend : HsType -> TermEncode (S n) a -> TermEncode n a
locallyExtend s x = do
  (i, fs) <- get
  pure $ evalState x (i, (s::fs))
-}

hsTypeName : HsType -> Name
hsTypeName HsVoid = "Void"
hsTypeName HsUnit = "Unit"
hsTypeName (HsTuple xs) = "Prod" ++ (concatMap (assert_total hsTypeName) xs)
hsTypeName (HsSum a b) = "Sum" ++ hsTypeName a ++ hsTypeName b
hsTypeName (HsVar v) = v
hsTypeName (HsParam n xs) = n ++ (concatMap (assert_total hsTypeName) xs)
hsTypeName (HsArrow a b) = "Arrow" ++ hsTypeName a ++ hsTypeName b

freshEnvWithTerms : String -> Vect n (HsType, HsTerm)
freshEnvWithTerms f = map (\ x => (x, HsTermVar (f ++ uppercase (hsTypeName x)))) freshEnv


encodeName : HsType -> Name
encodeName ty = "encode" ++ (uppercase (hsTypeName ty))

encoderTerm : TDef n -> TermEncode n HsTerm
encoderTerm (TApp f xs) = do
  xs' <- traverse (assert_total $ encoderTerm) xs
  pure (HsApp (HsFun ("encode" ++ (uppercase $ name f))) (toList xs'))
encoderTerm td = do
  env <- envTypes
  let varEncoders = map (\ x => HsTermVar (encodeName x))
                        (getUsedVars env td)
  pure $ HsApp (HsFun (encodeName (makeType freshEnv td))) (toList varEncoders)

decodeName : HsType -> Name
decodeName td = "decode" ++ (uppercase (hsTypeName td))

decoderTerm : TDef n -> TermEncode n HsTerm
decoderTerm (TApp f xs) = do
  xs' <- traverse (assert_total $ decoderTerm) xs
  pure (HsApp (HsFun ("decode" ++ (uppercase $ name f))) (toList xs'))
decoderTerm td = do
  env <- envTypes
  let varEncoders = map (\ x => HsTermVar (decodeName x))
                        (getUsedVars env td)
  pure $ HsApp (HsFun (decodeName (makeType freshEnv td))) (toList varEncoders)



dependencies : Vect n HsType -> TDef n -> List (m ** TNamed m)
dependencies fs td =
  nubBy (\ (m ** t), (m' ** t') => heteroEqNamed t t')
       (go fs td)
  where
  mutual
    goMu : Vect n HsType -> Vect k (String, TDef (S n)) -> List (m ** TNamed m)
    goMu fs tds = concatMap (assert_total $ go ((makeType fs (TMu tds))::fs) . snd) tds

    go : Vect n HsType -> TDef n -> List (m ** TNamed m)
    go fs T0 = []
    go fs T1 = []
    go fs (TSum xs) = concatMap (assert_total $ go fs) xs
    go fs (TProd xs) = concatMap (assert_total $ go fs) xs
    go fs (TVar v)    = []
    go {n = n} fs t@(TMu tds) = (n ** TName (nameMu tds) t) :: goMu fs tds
    go {n = n} fs (TApp {k = k} t@(TName name td) xs) =
        let env = map (makeType fs) xs
            depTd = case td of -- skip the TMu itself
                     TMu tds => goMu env tds
                     _       => go env td
            fixup = (\ x => case x of
                              TApp f xs' => [] -- will be counted later
                              _          => [(n ** TName "" x)]) in
        [(k**t)] ++ depTd ++ (concatMap fixup xs) ++ (concatMap (assert_total $ go fs) xs)

-- ||| Given a TDef and a Haskell term variable, gives a Haskell term
-- ||| of type Builder
encode : TDef n -> HsTerm -> TermEncode n HsTerm
encode T0 t = pure (hsAbsurd t)
encode T1 t = pure hsEmpty
encode (TSum td) t = do
  summands <- injectionInv td
  pure $ HsCase t (map (\ (lhs, i, rhs) => (lhs, word i <> rhs)) summands)
 where injectionInv : Vect (2 + k) (TDef n) -> TermEncode n (List (HsTerm, Int, HsTerm))
       injectionInv [a, b] = do
            [freshPV] <- freshVars 1 "z"
            a' <- encode a freshPV
            b' <- encode b freshPV
            pure [ (left freshPV, 0, a')
                 , (right freshPV, 1, b')
                 ]
       injectionInv (a::b::c::tds) = do
            [freshPV] <- freshVars 1 "z"
            a' <- encode a freshPV
            rest <- injectionInv (b::c::tds)
            pure $ (left freshPV, 0, a') ::
                     (map (\ (lhs, i, rhs) => (right lhs, i + 1, rhs)) rest)
encode (TProd {k} td) t = do
   freshPVs <- freshVars (2 + k) "y"
   factors <- mapWithIndexA (\ i, t' => assert_total $ encode (index i td) t') freshPVs
   pure $ HsCase t [(HsTupC freshPVs, HsConcat (toList factors))]
encode (TVar i) t = do
  encoders <- envTerms
  pure $ HsApp (index i encoders) [t]
encode t@(TMu tds) y = do
  eTerm <- encoderTerm t
  pure $ HsApp eTerm [y] -- assumes the def of eTerm is generated elsewhere
encode t@(TApp f xs) y = do
  eTerm <- encoderTerm t
  pure $ HsApp eTerm [y] -- assumes the def of eTerm is generated elsewhere

{-
||| Generate code for a TMu with name `encoderName` and body `tds`
encodeTMu : String -> Vect k (String, TDef (S n)) -> TermEncode n Haskell
encodeTMu {k = k} tname tds = do
  encoderVars <- envTypes
  let eName = HsParam tname [] -- TODO freshEnv
  locallyExtend eName $ do
    let funType = HsArrow eName hsByteString
    args <- mapWithIndexA f tds
    pure $ FunDef (encodeName eName) funType (toList args)
 where f : Fin k -> (String, TDef (S n)) -> TermEncode (S n) (List HsTerm, HsTerm)
       f i (name, T1) = pure ([HsInn name []], hstoBS $ word (fromInteger (finToInteger i)))
       f i (name, args) = do
         [freshPV] <- freshVars 1 "x"
         rhs <- assert_total $ encode args freshPV
         pure ([HsInn name [freshPV]], simplify $ hstoBS $ word (fromInteger (finToInteger i)) <> rhs)
-}

||| Given a TDef t, gives a Haskell term of type Deserialiser [[ t ]]
||| where [[ t ]] is the interpretation of t as a type
decode : TDef n -> TermEncode n HsTerm
decode T0 = pure hsFailDecode
decode T1 = pure $ hsReturn HsUnitTT
decode (TSum {k = k} tds) = do
  cases <- mapWithIndexA f tds
  [i] <- freshVars 1 "i"
  pure $ HsDo [(Just i, hsReadInt (fromNat k))
              , (Nothing, hsCaseDef i (toList cases) hsFailDecode)]
 where injection : Fin l -> HsTerm -> HsTerm
       injection FZ x = left x
       injection {l = S (S Z)} (FS FZ) x = right x
       injection (FS i) x = right (injection i x)
       f : Fin (2 + k) -> TDef n -> TermEncode n (HsTerm, HsTerm)
       f i t = do
          t' <- assert_total $ decode t
          [y] <- freshVars 1 "y"
          pure (HsInt (finToInteger i), HsDo [(Just y, t'), (Nothing, hsReturn (injection i y))])
decode (TProd {k = k} xs) = do
  vs <- freshVars (2 + k) "x"
  xs' <- mapWithIndexA (\ i, x => do x' <- assert_total $ decode x; pure (Just (index i vs), x')) xs
  pure (HsDo $ (toList xs') ++ [(Nothing, hsReturn (HsTupC vs))])
decode (TVar i) = do
  decoders <- envTerms
  pure $ index i decoders
decode t@(TMu tds)   = decoderTerm t -- assumes the def of this is generated elsewhere
decode t@(TApp f xs) = decoderTerm t -- assumes the def of this is generated elsewhere

encodeDef : TNamed n -> Haskell
encodeDef {n} t@(TName tname td) =
  let env = freshEnvWithTerms "encode"
      funName = if tname == ""
                then encodeName (makeType (freshEnv {n}) td)
                else "encode" ++ uppercase tname
      varEncs = toList $ map snd env
      currTerm = HsApp (HsFun funName) varEncs
      currType = if tname == ""  -- makeType' env t
                 then makeType (freshEnv {n}) td
                 else HsParam tname []
      funType = foldr HsArrow (hsSerialiser (makeType' (freshEnv {n}) t)) (map hsSerialiser (freshEnv {n}))
      clauses = genClauses n currType currTerm env varEncs td in
      FunDef funName funType clauses
  where genConstructor : (n : Nat) -> String -> TDef n -> TermEncode n (HsTerm, List HsTerm)
        genConstructor n name (TProd {k = k} xs) = do
          xs' <- freshVars (2 + k) "x"
          rhs <- mapWithIndexA (\ i, t' => assert_total $ encode (index i xs) t') xs'
          pure $ (HsInn name (toList xs'), toList rhs)
        genConstructor n name td = do
          [x'] <- freshVars 1 "x"
          rhs <- assert_total $ encode td x'
          pure $ (HsInn name [x'], [rhs])

        genClause : (n : Nat) -> List HsTerm -> Fin k -> (String, TDef n) -> TermEncode n (List HsTerm, HsTerm)
        genClause n varEncs i (name, T1) = pure (varEncs ++ [HsInn name []], word (fromInteger (finToInteger i)))
        genClause n varEncs i (name, args) = do
          (con, rhs) <- genConstructor n name args
          pure (varEncs ++ [con], simplify $ HsConcat (word (fromInteger (finToInteger i))::rhs))

        -- Idris is not clever enough to figure out the following type if written as a case expression
        genClauses : (n : Nat) -> HsType -> HsTerm -> Vect n (HsType, HsTerm) -> List HsTerm -> TDef n -> List (List HsTerm, HsTerm)
        genClauses n currType currTerm env varEncs (TMu tds) = toList $ runTermEncode ((currType, currTerm)::env) (mapWithIndexA (genClause (S n) varEncs) tds)
        genClauses n currType currTerm env varEncs td        = let v = HsTermVar "x" in [( varEncs ++ [v] , simplify $ runTermEncode env (encode td v))]

decodeDef : TNamed n -> Haskell
decodeDef {n = n} t@(TName tname td) =
  let env = freshEnvWithTerms "decode"
      funName = if tname == ""
                then decodeName (makeType (freshEnv {n}) td)
                else "decode" ++ uppercase tname
      varEncs = toList $ map snd env
      currTerm = HsApp (HsFun funName) varEncs
      currType = if tname == ""  -- makeType' env t
                 then makeType (freshEnv {n}) td
                 else HsParam tname []
      funType = foldr HsArrow (hsDeserialiser (makeType' (freshEnv {n}) t)) (map hsDeserialiser (freshEnv {n}))
      rhs = genCase n currType currTerm env td in
      FunDef funName funType [(varEncs, rhs)]
  where genConstructor : (n : Nat) -> String -> TDef n -> TermEncode n (List (HsTerm, HsTerm))
        genConstructor n name (TProd {k = k} xs) = do
          vs <- freshVars (2 + k) "x"
          xs' <- mapWithIndexA (\ i, x => do x' <- assert_total $ decode x; pure (index i vs, x')) xs
          pure $ toList xs'
        genConstructor n name td = do
          [v] <- freshVars 1 "x"
          xs' <- assert_total $ decode td
          pure $ [(v, xs')]

        genCases : (n : Nat) -> Fin k -> (String, TDef n) -> TermEncode n (HsTerm, HsTerm)
        genCases n i (name, T1) = pure (HsInt (finToInteger i), hsReturn (HsInn name []))
        genCases n i (name, args) = do
          args' <- genConstructor n name args
          pure (HsInt (finToInteger i), HsDo $ (map (\ (x, e) => (Just x, e)) args')++[(Nothing, hsReturn (HsInn name (map fst args')))])

        -- Idris is not clever enough to figure out the following type if written as a case expression
        genCase : (n : Nat) -> HsType -> HsTerm -> Vect n (HsType, HsTerm) -> TDef n -> HsTerm
        genCase n currType currTerm env (TMu {k = k} tds) = runTermEncode ((currType, currTerm)::env) $ do
              cases <- mapWithIndexA (genCases (S n)) tds
              [i] <- freshVars 1 "i"
              pure $ HsDo [(Just i, hsReadInt (fromNat k))
                          ,(Nothing, simplify $ hsCaseDef i (toList cases) hsFailDecode)]
        genCase n currType currTerm env td = simplify $ runTermEncode env (decode td)

ASTGen Haskell HsType n where
  msgType           = makeType' freshEnv
  generateTyDefs tn = reverse $ evalState (makeDefs' tn) []
  generateTermDefs tn =
    let deps = concatMap (\ (m**t) => [encodeDef t, decodeDef t]) (dependencies freshEnv (def tn)) in
        deps ++ [encodeDef tn, decodeDef tn]

CodegenIndep Haskell HsType where
  typeSource = renderType
  defSource  = renderDef
  preamble    = text """import Data.Word
import Data.ByteString.Lazy
import Data.ByteString.Builder

type Serialiser a = a -> Builder

runSerialiser :: Serialiser a -> a -> ByteString
runSerialiser f = toLazyByteString . f

newtype Deserialiser a  = MkDeserialiser (ByteString -> Maybe (a, ByteString))

runDeserialiser :: Deserialiser a -> ByteString -> Maybe (a, ByteString)
runDeserialiser (MkDeserialiser f) = f

instance Functor Deserialiser where
  fmap f da = MkDeserialiser (\ bs -> do
    (a', bs') <- runDeserialiser da bs
    Just (f a', bs'))


instance Applicative Deserialiser where
  pure x = MkDeserialiser (\ bs -> Just (x, bs))
  df <*> da =  MkDeserialiser (\ bs -> do
    (f', bs') <- runDeserialiser df bs
    (a', bs'') <- runDeserialiser da bs'
    Just (f' a', bs''))


instance Monad Deserialiser where
  (MkDeserialiser a) >>= g = MkDeserialiser (\ bs -> do
    (a', bs') <- a bs
    let (MkDeserialiser ga') = g a'
    ga' bs')

failDecode :: Deserialiser a
failDecode = MkDeserialiser (\ bs -> Nothing)

deserialiseInt :: Deserialiser Integer
deserialiseInt = MkDeserialiser (\ bs -> fmap go (uncons bs))
  where go :: (Word8, ByteString) -> (Integer, ByteString)
        go (b, bs') = (toInteger b, bs')"""


g : TNamed 0
g = TName "ListNat" (TMu [("Nil", T1), ("Cons", TProd [(TMu [("Zero", T1), ("Suc", TVar 0)]), TVar 0])])

bit : TNamed 0
bit = TName "Bit" $ TSum [T1, T1]

byte : TNamed 0
byte = TName "Byte" $ powN 8 bit

list : TNamed 1
list = TName "List" $ TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

listAlphaOrBeta : TNamed 2
listAlphaOrBeta = TName "listAlphaOrBeta" $ TApp list [TSum [TVar 0, TVar 1]]

listBitOrByte : TNamed 0
listBitOrByte = TName "listBitOrByte" $ TApp listAlphaOrBeta [wrap bit, wrap byte]


test : TNamed n -> IO ()
test = putStrLn . toString . vsep2 . map renderDef . generateTermDefs

{-

-- TODO: move tests


t' : TDef 0 -> String
t' = toString . vsep2 . map renderDef . termdefDecode


nat : TDef 1 -- weakened to be used in `rose`
nat = TMu [("Zero", T1), ("Suc", TVar 0)]

rose : TDef 0
rose = TMu [("Leaf", nat), ("Branch", TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])] )]
-}

-- TODO: optimise Mu with one argument
-- TODO: proper doc strings
-- TODO: getUsedVars
-- TODO: prettyprinting HsArrow
-- TODO: wrap vs lift in dependencies
