module Backend.Haskell

import Types
import Typedefs

import Backend
import Backend.Utils

import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect

%default total
%access public export

||| The syntactic structure of Haskell types.
data HsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  HsVoid  :                                HsType

  ||| The `()` (i.e. unit/singleton) type.
  HsUnit  :                                HsType

  ||| The tuple type, containing two or more further types.
  HsTuple :         Vect (2 + n) HsType -> HsType

  ||| A type variable.
  HsVar   :         Name                -> HsType

  ||| A named type with zero or more other types as parameters.
  HsParam : Name -> Vect n HsType       -> HsType

  ||| A function type (only used for top-level type of termdef
  ||| decoders and encoders)
  HsArrow :         HsType -> HsType    -> HsType

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
  HsInn : Name -> Vect n HsTerm -> HsTerm

  ||| A case expression, containing a term being examined, and a list
  ||| of (lhs, rhs) pairs. Invariants: lhs is a pattern (ie all
  ||| variables occur linearly), and FreeVars(rhs) \subseteq
  ||| FreeVars(lhs).
  HsCase : HsTerm -> Vect n (HsTerm, HsTerm) -> HsTerm

  ||| A function application
  HsApp : HsTerm -> Vect n HsTerm -> HsTerm

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
  HsConcat : Vect k HsTerm -> HsTerm

||| The syntactic structure of Haskell type declarations.
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect n (Name, HsType) -> Haskell

  ||| A function definition is a declared name, a type, and a list of
  ||| clauses of the form ((arg1, ..., argk), rhs)
  FunDef : Name -> HsType -> Vect n (List HsTerm, HsTerm) -> Haskell

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
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)
  renderType (HsArrow a b)         = (guardParen a) |++| text "->" |++| (guardParen b)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : HsType -> Doc
  guardParen t@(HsParam _ []) = assert_total $ renderType t
  guardParen t@(HsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t@(HsArrow _ _)  = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

mutual
  ||| Render a term as Haskell source code.
  renderTerm : HsTerm -> Doc
  renderTerm HsUnitTT         = text "()"
  renderTerm (HsTupC xs) = tupled . toList . map (assert_total guardParenTerm) $ xs
  renderTerm (HsTermVar x)    = text x
  renderTerm HsWildcard       = text "_"
  renderTerm (HsInn name args) = text name |++| hsep (toList $ map (assert_total guardParenTerm) $ args)
  renderTerm (HsCase t bs)  = align $ text "case" |++| align (renderTerm t) |++| text "of" |+| breakLine
      |+| indent 2
           (vsep (toList (map (hang 2 . (assert_total $ renderCase)) bs)))
    where
    renderCase : (HsTerm, HsTerm) -> Doc
    renderCase (lhs, rhs) = renderTerm lhs |++| text "->" |++| (renderTerm rhs)
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
  renderTerm (HsConcat xs) = text "mconcat" |++| (list . toList . map (assert_total guardParenTerm) $ xs)

  ||| As `renderTerm`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParenTerm : HsTerm -> Doc
  guardParenTerm t@(HsInn _ (a::as)) = parens (assert_total $ renderTerm t)
  guardParenTerm t@(HsCase _ _) = parens (assert_total $ renderTerm t)
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
simplify t = t

anonMu : Vect n (Name, a) -> Name
anonMu = concatMap (uppercase . fst)

||| Generate a Haskell type from a `TDef`.
makeType : Env n -> TDef n -> HsType
makeType _ T0             = HsVoid
makeType _ T1             = HsUnit
makeType e (TSum xs)      = foldr1' (\t1,t2 => HsParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType e (TProd xs)     = HsTuple $ map (assert_total $ makeType e) xs
makeType e (TVar v)       = either HsVar hsParam $ Vect.index v e
  where
  hsParam : Decl -> HsType
  hsParam (MkDecl n ps) = HsParam n (map HsVar ps)
makeType e td@(TMu cases) = HsParam (anonMu cases) . map HsVar $ getFreeVars (getUsedVars e td)
makeType e (TApp f xs)    = HsParam (name f) (map (assert_total $ makeType e) xs)

makeType' : Env n -> TNamed n -> HsType
makeType' e (TName name body) = HsParam name . map HsVar $ getFreeVars (getUsedVars e body)

mutual
  ||| Generate Haskell type definitions from a `TDef`, including all of its dependencies.
  makeDefs : TDef n -> State (List Name) (List Haskell)
  makeDefs T0            = pure []
  makeDefs T1            = pure []
  makeDefs (TProd xs)    = map concat $ traverse (assert_total makeDefs) xs
  makeDefs (TSum xs)     = map concat $ traverse (assert_total makeDefs) xs
  makeDefs (TVar v)      = pure []
  makeDefs (TApp f xs) = do
      res <- assert_total $ makeDefs' f
      res' <- concat <$> traverse (assert_total makeDefs) xs
      pure (res ++ res')
  makeDefs td@(TMu cases) = makeDefs' $ TName (anonMu cases) td -- We name anonymous mus using their constructors.

  makeDefs' : TNamed n -> State (List Name) (List Haskell)
  makeDefs' (TName name body) = do
      st <- get
      if List.elem name st then pure []
      else do
        let decl = MkDecl name (getFreeVars $ getUsedVars (freshEnvLC _) body)
        put (name :: st)
        case body of
          TMu cases => do -- Named `TMu`s are treated as ADTs.
            let newEnv = Right decl :: freshEnvLC _
            let args = map (map (makeType newEnv)) cases
            res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs bdy) (toList cases)
            pure $ ADT decl args :: res
          _         => do -- All other named types are treated as synonyms.
            res <- assert_total $ makeDefs body
            pure $ Synonym decl (makeType (freshEnvLC n) body) :: res

Backend Haskell where
  generateTyDefs e td = reverse $ evalState (makeDefs td) []
  generateCode        = renderDef
  freshEnv            = freshEnvLC

-------- Termdefs -------------------------------------------

hsAbsurd : HsTerm -> HsTerm
hsAbsurd t = HsApp (HsFun "absurd") [t] -- `absurd :: Void -> a` from Data.Void

hsEmpty : HsTerm
hsEmpty = HsFun "mempty" -- `mempty :: Builder` from Data.ByteString.Builder

||| `toLazyByteString :: Builder -> ByteString` from Data.ByteString.Builder
hstoBS : HsTerm -> HsTerm
hstoBS t = HsApp (HsFun "toLazyByteString") [t]

hsByteString : HsType
hsByteString = HsParam "ByteString" []

hsDeserializer : HsType -> HsType
hsDeserializer a = HsParam "Deserializer" [a]

||| `runDeserializer :: Deserializer a -> ByteString -> Maybe (a, ByteString)`
hsrunDeserializer : HsTerm -> HsTerm
hsrunDeserializer d = HsApp (HsFun "runDeserializer") [d]


||| `deserializeInt :: Deserializer Integer`; the argument
||| denotes how many bits should be read (currently ignored)
hsReadInt : Integer -> HsTerm
hsReadInt k = HsApp (HsFun "deserializeInt") [] -- [HsInt k]

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

hsCaseDef : HsTerm -> Vect n (HsTerm, HsTerm) -> HsTerm -> HsTerm
hsCaseDef t cases def = HsCase t (cases ++ [(HsWildcard, def)])

infixr 10 <>
private
(<>) : HsTerm -> HsTerm -> HsTerm
a <> b = HsConcat [a, b]

private
word : Int -> HsTerm
word i = HsApp (HsFun "word8") [HsWord8 i] -- `word8 :: Word8 -> Builder` from Data.ByteString.Builder

derivedName : TDef n -> Name
derivedName T0 = "Void"
derivedName T1 = "Unit"
derivedName (TSum xs) = "Sum" ++ (concatMap (assert_total derivedName) xs)
derivedName (TProd xs) = "Prod" ++ (concatMap (assert_total derivedName) xs)
derivedName (TVar v)    = "error: deriving name of type variable" -- should never happen
derivedName (TMu tds) = "Mu" ++ (anonMu tds)
derivedName (TApp f xs) = assert_total $ derivedName (ap (td f) xs)



encodeName : TDef n -> Name
encodeName td = "encode" ++ derivedName td

decodeName : TDef n -> Name
decodeName td = "decode" ++ derivedName td

mapWithIndexA : Applicative m => {n : Nat} -> (Fin n -> a -> m b) -> Vect n a -> m (Vect n b)
mapWithIndexA f [] = pure []
mapWithIndexA f (a::as) = pure (::) <*> f FZ a <*> mapWithIndexA (f . FS) as

-- ||| Monad for term encoding generator, keeping track of a name
-- ||| supply and a function to apply for each type variable
TermEncode : Nat -> Type -> Type
TermEncode n = State (List String, Vect n String)

runTermEncode : Vect n String -> TermEncode n a -> a
runTermEncode fs mx = evalState mx ([], fs)

encoderList : TermEncode n (Vect n String)
encoderList = do
  (_, fs) <- get
  pure fs

freshVars : (k : Nat) -> String -> TermEncode n (Vect k HsTerm)
freshVars Z suggestion = pure []
freshVars (S n) suggestion = do
  (used, fs) <- get
  let fresh = if not (suggestion `elem` used) then suggestion
                                              else countUp 0 suggestion used
  put (fresh::used, fs)
  rest <- freshVars n suggestion
  pure $ (HsTermVar fresh) :: rest

locallyExtend : String -> TermEncode (S n) a -> TermEncode n a
locallyExtend s x = do
  (i, fs) <- get
  pure $ evalState x (i, (s::fs))

allMuInside : ({l : Nat} -> (TDef l -> Name)) -> TDef 0 -> List (m ** k ** (Vect k (String, TDef (S m)), Vect m String))
allMuInside namer t = nubBy (\ (m ** k ** (td, fs)), (m' ** k' ** (td', fs')) => heteroEq (TMu td) (TMu td')) (go [] t) where
  go : Vect n String -> TDef n -> List (m ** k ** (Vect k (String, TDef (S m)), Vect m String))
  go fs T0 = []
  go fs T1 = []
  go fs (TSum xs) = concatMap (assert_total $ go fs) xs
  go fs (TProd xs) = concatMap (assert_total $ go fs) xs
  go fs (TVar v)    = []
  go {n = n} fs (TMu {k = k} tds) = (n ** k ** (tds, fs)) ::  (concatMap (assert_total $ go ((namer (TMu tds)) :: fs) . snd) tds)
  go fs (TApp f xs) = assert_total $ go fs (ap (td f) xs)

-- ||| Given a TDef and a Haskell term variable, gives a Haskell term
-- ||| of type Builder
encode : TDef n -> HsTerm -> TermEncode n HsTerm
encode T0 t = pure (hsAbsurd t)
encode T1 t = pure hsEmpty
encode (TSum td) t = do
  summands <- injectionInv td
  pure $ HsCase t (map (\ (lhs, i, rhs) => (lhs, word i <> rhs)) summands)
 where injectionInv : Vect (2 + k) (TDef n) -> TermEncode n (Vect (2 + k) (HsTerm, Int, HsTerm))
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
   pure $ HsCase t [(HsTupC freshPVs, HsConcat factors)]
encode (TVar i) t = do
  encoders <- encoderList
  pure $ HsApp (HsFun (index i encoders)) [t]
encode {n = n} (TMu {k} td) t = pure $ HsApp (HsFun (encodeName (TMu td))) [t] -- assumes this is generated elsewhere
encode (TApp f xs) t = assert_total $ encode (ap (td f) xs) t

encodeTMu : Vect k (String, TDef (S n)) -> TermEncode n Haskell
encodeTMu {k = k} tds = locallyExtend (encodeName (TMu tds)) $ do
  let funType = HsArrow (HsParam (anonMu tds) []) hsByteString
  args <- mapWithIndexA f tds
  pure $ FunDef (encodeName (TMu tds)) funType args
 where f : Fin k -> (String, TDef (S n)) -> TermEncode (S n) (List HsTerm, HsTerm)
       f i (name, T1) = pure ([HsInn name []], hstoBS $ word (fromInteger (finToInteger i)))
       f i (name, args) = do
         [freshPV] <- freshVars 1 "x"
         rhs <- assert_total $ encode args freshPV
         pure ([HsInn name [freshPV]], hstoBS $ word (fromInteger (finToInteger i)) <> rhs)

-- TODO: need to carry environment?

||| Given a TDef t, gives a Haskell term of type Deserialiser [[ t ]]
||| where [[ t ]] is the interpretation of t as a type
decode : TDef n -> TermEncode n HsTerm
decode T0 = pure hsFailDecode
decode T1 = pure $ hsReturn HsUnitTT
decode (TSum {k = k} tds) = do
  cases <- mapWithIndexA f tds
  [i] <- freshVars 1 "i"
  pure $ HsDo [(Just i, hsReadInt (fromNat k))
              , (Nothing, hsCaseDef i cases hsFailDecode)]
 where injection : Fin l -> HsTerm -> HsTerm
       injection FZ x = left x
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
  decoders <- encoderList
  pure $ HsFun (index i decoders)
decode {n = n} (TMu {k} td) = pure $ (HsFun (decodeName (TMu td))) -- assumes this is generated elsewhere
decode (TApp f xs) = assert_total $ decode (ap (td f) xs)

decodeTMu : Vect k (String, TDef (S n)) -> TermEncode n Haskell -- TODO!!!
decodeTMu {k = k} tds = locallyExtend (decodeName (TMu tds)) $ do
  let funType = hsDeserializer (HsParam (anonMu tds) [])
  cases <- mapWithIndexA f tds
  [i] <- freshVars 1 "i"
  let rhs = HsDo [(Just i, hsReadInt (fromNat k))
                 ,(Nothing, hsCaseDef i cases hsFailDecode)]
  pure $ FunDef (decodeName (TMu tds)) funType [([], rhs)]
 where f : Fin k -> (String, TDef (S n)) -> TermEncode (S n) (HsTerm, HsTerm)
       f i (name, T1) = pure (HsInt (finToInteger i), hsReturn (HsInn name []))
       f i (name, args) = do
         rest <- assert_total $ decode args
         [x] <- freshVars 1 "x"
         pure (HsInt (finToInteger i), HsDo [(Just x, rest)
                                            ,(Nothing, hsReturn (HsInn name [x]))])

NewBackend Haskell HsType HsTerm where
  msgType          = makeType (freshEnv {lang=Haskell} 0)
  typedefs td      = reverse $ evalState (makeDefs td) []
  termdefEncode td@(TMu _) = map (\ (n ** k ** (tds, fs)) => runTermEncode fs (encodeTMu tds)) (allMuInside encodeName td)
  termdefEncode td =
    let deps = map (\ (n ** k ** (tds, fs)) => runTermEncode fs (encodeTMu tds)) (allMuInside encodeName td)
        funName = encodeName td
        funType = HsArrow (msgType {def=Haskell} td) hsByteString
        v = HsTermVar "x"
        rhs = hstoBS (runTermEncode [] (encode td v))
    in deps ++ [FunDef funName funType [([v], rhs)]]
  termdefDecode td@(TMu _) = map (\ (n ** k ** (tds, fs)) => runTermEncode fs (decodeTMu tds)) (allMuInside decodeName td)
  termdefDecode td =
    let deps = map (\ (n ** k ** (tds, fs)) => runTermEncode fs (decodeTMu tds)) (allMuInside decodeName td)
        funName = decodeName td
        funType = HsArrow hsByteString (HsParam "Maybe" [HsTuple [(msgType {def=Haskell} td), hsByteString]])
        rhs = hsrunDeserializer (simplify $ runTermEncode [] (decode td))
    in deps ++ [FunDef funName funType [([], rhs)]]
  source type defs = vsep2 $ map renderDef $ Synonym (MkDecl "TypedefSchema" []) type :: defs

||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv {lang=Haskell} n)

-- TODO: move tests

t : TDef 0 -> String
t = toString . vsep2 . map renderDef . termdefEncode

t' : TDef 0 -> String
t' = toString . vsep2 . map renderDef . termdefDecode

g : TDef 0
g = TMu [("Nil", T1), ("Cons", TProd [(TMu [("Zero", T1), ("Suc", TVar 0)]), TVar 0])]

nat : TDef 1 -- weakened to be used in `rose`
nat = TMu [("Zero", T1), ("Suc", TVar 0)]

rose : TDef 0
rose = TMu [("Leaf", nat), ("Branch", TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])] )]

-- TODO: add backend preamble

-- TODO: align case blocks

-- TODO: proper doc strings
