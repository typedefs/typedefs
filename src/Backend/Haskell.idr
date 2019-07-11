module Backend.Haskell

import Names
import Typedefs

import Backend
import Backend.Utils
import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect
import Data.NEList
import Data.SortedMap

%default total
%access export

-- Representing Haskell source code -----

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

||| The syntactic structure of (a subset of) Haskell terms.
data HsTerm : Type where
  ||| The unit term `()`.
  HsUnitTT  :                                         HsTerm

  ||| The tuple constructor, containing two or more further terms.
  HsTupC :            Vect (2 + n) HsTerm          -> HsTerm

  ||| A term variable, with a name (no need for deBruijn indices when terms are first-order!).
  HsTermVar : Name                                 -> HsTerm

  ||| The wildcard pattern `_`.
  HsWildcard  :                                       HsTerm

  ||| A data type constructor, containing a name and a list of further terms.
  HsInn :     Name -> List HsTerm                  -> HsTerm

  ||| A case expression, containing a term being examined, and a list
  ||| of (lhs, rhs) pairs. Invariants: lhs is a pattern (ie all
  ||| variables occur linearly), and FreeVars(rhs) \subseteq
  ||| FreeVars(lhs).
  HsCase : HsTerm ->  List (HsTerm, HsTerm)       -> HsTerm

  ||| A function application.
  HsApp : HsTerm   -> List HsTerm                 -> HsTerm

  ||| (The name of) a function.
  HsFun : Name                                    -> HsTerm

  ||| Do-notation: A list of statements of the form
  |||   x <- e    [ represented by (Just x, e)
  ||| or simply
  |||   e         [ represented by (Nothing, e)].
  HsDo :              List (Maybe HsTerm, HsTerm) -> HsTerm

  -- special constants (for convencience)

  ||| A Word8 converted from an Int literal (`fromIntegral i`).
  HsWord8 : Int                                   -> HsTerm

  ||| An Int literal.
  HsInt : Integer                                 -> HsTerm

  ||| `mconcat :: [Builder] -> Builder` from Data.ByteString.Builder.
  HsConcat :          List HsTerm                 -> HsTerm


||| The syntactic structure of Haskell type declarations.
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect n (Name, HsType) -> Haskell

  ||| A function definition is a declared name, a type, and a list of
  ||| clauses of the form ((arg1, ..., argk), rhs).
  FunDef : Name -> HsType -> List (List HsTerm, HsTerm) -> Haskell

-- Rendering Haskell source code -----

||| Render a name applied to a list of arguments exactly as written.
||| Arguments need to be previously parenthesized, if applicable.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

||| The same as `tupled : List Doc -> Doc`, except that tuples with
||| more than 62 components get turned into nested tuples, to adhere
||| to GHC's restriction on tuple size.
||| (See https://hackage.haskell.org/package/ghc-prim-0.5.1.0/docs/src/GHC.Tuple.html )
hsTupled : List Doc -> Doc
hsTupled xs = if length xs < 63
              then tupled xs
              else let (xs0, xs1) = splitAt 61 xs in
                     tupled (xs0 ++ [hsTupled $ assert_smaller xs xs1])


mutual
  ||| Render a type signature as Haskell source code.
  renderType : HsType -> Doc
  renderType HsVoid                = text "Void"
  renderType HsUnit                = text "()"
  renderType (HsTuple xs)          = hsTupled . toList . map (assert_total renderType) $ xs
  renderType (HsSum a b)           = renderApp "Either" [guardParen a, guardParen b]
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)
  renderType (HsArrow a b)         = renderArrow (renderParamNoParen a) b
    where
      -- Parenthesize, except for Param (since e.g. type application binds stronger than ->)
      renderParamNoParen : HsType -> Doc
      renderParamNoParen a@(HsParam _ _) = renderType a
      renderParamNoParen a               = guardParen a

      renderArrow : Doc -> HsType -> Doc
      renderArrow a (HsArrow b' c') = a |++| text "->" |++| (renderArrow (renderParamNoParen b') c')
      renderArrow a b               = a |++| text "->" |++| (renderParamNoParen b)


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
  renderTerm  HsUnitTT         = text "()"
  renderTerm (HsTupC xs)       = tupled . toList . map (assert_total guardParenTerm) $ xs
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
private
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
private
freshEnvWithTerms : (prefix : String) -> Vect n (HsType, HsTerm)
freshEnvWithTerms prefix = map (\ x => (x, HsTermVar (prefix ++ uppercase (hsTypeName x)))) freshEnv

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
makeType' e (TName ""   body) = makeType e body --escape hatch; used e.g. for all non-TApp dependencies of a TApp
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
  makeDefs    (TApp f xs) = 
    do res <- assert_total $ makeDefs' f
       res' <- concat <$> traverse (assert_total makeDefs) xs
       pure (res ++ res')

  ||| Generate Haskell type definitions for a `TNamed` and all of its dependencies.
  makeDefs' : TNamed n -> State (List Name) (List Haskell)
  makeDefs' (TName name body) = ifNotPresent name $
      let freshEnvString = map (\ x => case x of HsVar v => v; _ => "") freshEnv
          decl = MkDecl name (getUsedVars freshEnvString body) in
      case body of
        TMu cases => -- Named `TMu`s are treated as ADTs.
          do let newEnv = hsParam decl :: freshEnv
             let args = map (map (makeType newEnv)) cases
             res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs bdy) (toList cases)
             pure $ ADT decl args :: res
        _ => -- All other named types are treated as synonyms.
          do res <- assert_total $ makeDefs body
             pure $ Synonym decl (makeType freshEnv body) :: res

-- Convenience definitions for Termdefs -----

-- `absurd :: Void -> a` from Data.Void
private
hsAbsurd : HsTerm -> HsTerm
hsAbsurd t = HsApp (HsFun "absurd") [t]

-- `mempty :: Builder` from Data.ByteString.Builder
private
hsEmpty : HsTerm
hsEmpty = HsFun "mempty"

-- `Deserialiser` type family
private
hsDeserialiser : HsType -> HsType
hsDeserialiser a = HsParam "Deserialiser" [a]

-- `Serialiser` type family
private
hsSerialiser : HsType -> HsType
hsSerialiser a = HsParam "Serialiser" [a]

-- `deserialiseInt :: Deserialiser Integer`
-- @k how many bits should be read (currently ignored)
private
hsReadInt : Integer -> HsTerm
hsReadInt k = HsApp (HsFun "deserialiseInt") [] -- [HsInt k]

-- `failDecode :: Deserialiser a`
private
hsFailDecode : HsTerm
hsFailDecode = HsFun "failDecode"

-- `return :: a -> Deserialiser a`
private
hsReturn : HsTerm -> HsTerm
hsReturn x = HsApp (HsFun "return") [x]

-- `Left : a -> Either a b`
private
hsLeft : HsTerm -> HsTerm
hsLeft x = HsInn "Left" [x]

-- `Right : b -> Either a b`
private
hsRight : HsTerm -> HsTerm
hsRight x = HsInn "Right" [x]

-- `case t of cases; _ -> def`
private
hsCaseDef : HsTerm -> List (HsTerm, HsTerm) -> HsTerm -> HsTerm
hsCaseDef t cases def = HsCase t (cases ++ [(HsWildcard, def)])

-- `word8 :: Word8 -> Builder` from Data.ByteString.Builder
private
word : Int -> HsTerm
word i = HsApp (HsFun "word8") [HsWord8 i]

-- The TermGen monad -----

||| Monad for the term generator, keeping track of a name supply (in
||| the form of a map of the number of usages for each name) and a
||| "semantic" environment consisting of an environment of types, and
||| terms for decoding/encoding the types.
||| @ n the size of the environment
TermGen : (n : Nat) -> Type -> Type
TermGen n = State (SortedMap String Nat, Vect n (HsType,HsTerm))

||| Given an environment, run the term generator, with no names
||| already used to start with.
|||| @ env environment to use
runTermGen : (env : Vect n (HsType,HsTerm)) -> TermGen n a -> a
runTermGen env mx = evalState mx (empty, env)

||| Extract an environment of types.
envTypes : TermGen n (Vect n HsType)
envTypes = do (_, fs) <- get
              pure $ map fst fs

||| Extract an environment of encoder/decoder terms.
envTerms : TermGen n (Vect n HsTerm)
envTerms = do (_, fs) <- get
              pure $ map snd fs

||| Generate a vector of fresh variables, using a given string as a
||| name suggestion.
||| @ k number of variables to generate
||| @ suggestion name to use if possible
freshVars : (k : Nat) -> (suggestion : String) -> TermGen n (Vect k HsTerm)
freshVars Z suggestion = pure []
freshVars k@(S n) suggestion = 
  do (alreadyUsed, fs) <- get
     let currentCount = maybe 0 id (SortedMap.lookup suggestion alreadyUsed)
     let newUsed = insert suggestion (fromNat $ (toNat currentCount) + k) (delete suggestion alreadyUsed)
     put (newUsed, fs)
     pure $ map (\ i => HsTermVar $ suggestion ++ (showVar $ currentCount + (toNat i))) range
 where
   -- We want x, x0, x1, ...
   showVar : Nat -> String
   showVar Z = ""
   showVar (S n) = show n

||| Name to use for encoder at this type.
encodeName : HsType -> Name
encodeName ty = "encode" ++ (uppercase $ hsTypeName ty)

||| Name to use for decoder at this type.
decodeName : HsType -> Name
decodeName ty = "decode" ++ (uppercase $ hsTypeName ty)

||| Term to use for encoder/decoder for the given `TDef`.
||| @ namer should be either `encodeName` or `decodeName`; determines if
|||         we generate the encoder or decoder term.
encoderDecoderTerm : (namer : HsType -> Name) -> TDef n -> TermGen n HsTerm
encoderDecoderTerm namer (TApp g xs) = 
  do xs' <- traverse (assert_total $ encoderDecoderTerm namer) xs
     pure (HsApp (HsFun (namer (HsParam (name g) []))) (toList xs'))
encoderDecoderTerm namer (TVar i)    = 
  do env <- envTerms
     pure (index i env)
encoderDecoderTerm namer td          = 
  do env <- envTerms
     let varEncoders = getUsedVars env td
     pure $ HsApp (HsFun (namer (makeType freshEnv td))) (toList varEncoders)

||| Term to use for encoder for this `TDef`.
encoderTerm : TDef n -> TermGen n HsTerm
encoderTerm td = encoderDecoderTerm encodeName td

||| Term to use for encoder for this `TDef`.
decoderTerm : TDef n -> TermGen n HsTerm
decoderTerm td = encoderDecoderTerm decodeName td

||| Compute the list of `TNamed`s whose termdefs the termdef for the
||| given `TDef` depends on. Does not include the given `TDef` itself.
||| @ env semantic environment, used for knowing what to name things
dependencies : (env : Vect n HsType) -> TDef n -> List (m ** TNamed m)
dependencies env td =
  filter (\ (m ** t) => not $ heteroEq (def t) td)
    (nubBy (\ (m ** t), (m' ** t') => heteroEqNamed t t') (go env td))
  where
  mutual
    goMu : Vect n HsType -> Vect k (String, TDef (S n)) -> List (m ** TNamed m)
    goMu env tds = concatMap (assert_total $ go ((makeType env (TMu tds))::env) . snd) tds

    -- We return a TNamed here, because we still have access to the name information
    go : Vect n HsType -> TDef n -> List (m ** TNamed m)
    go     env    T0                             = []
    go     env    T1                             = []
    go     env   (TSum xs)                       = concatMap (assert_total $ go env) xs
    go     env   (TProd xs)                      = concatMap (assert_total $ go env) xs
    go     env   (TVar v)                        = []
    go {n} env t@(TMu tds)                       = (n ** TName (nameMu tds) t) :: goMu env tds
    go     env   (TApp {k} t@(TName name td) xs) =
      let envxs = map (makeType env) xs
          -- dependencies of the actual td
          depTd = case td of
                   TMu tds => goMu envxs tds -- skip the TMu itself
                   _       => go envxs td 
        in
      depTd ++ [(k**t)] ++ (concatMap (assert_total $ go env) xs) ++ (concatMap fixup xs)
      where
         -- function to fix up some unwanted entries
        fixup : {l : Nat} -> TDef l -> List (m ** TNamed m)
        fixup (TApp f xs) = [] -- will be counted later
        fixup (TVar i)    = [] -- will be a parameter anyway
        fixup {l} x       = [(l ** TName "" x)]

||| Given a TDef `td` and a Haskell term t of type [[ td ]] (where
||| [[ td ]] is the interpretation of td as a type), constructs a
||| Haskell Term of type `Builder`.
||| @ td TDef to build term for
||| @ t Haskell term of the TDef type the encoder should be applied to
encode : (td : TDef n) -> (t : HsTerm) -> TermGen n HsTerm
encode    T0            t = pure (hsAbsurd t)
encode    T1            t = pure hsEmpty
encode   (TSum td)      t = 
  do summands <- injectionInv td
     pure $ HsCase t (map (\ (lhs, i, rhs) => (lhs, HsConcat [word i, rhs])) summands)
 where 
  injectionInv : Vect (2 + k) (TDef n) -> TermGen n (List (HsTerm, Int, HsTerm))
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
     factors <- mapWithIndexA (\ i, t' => assert_total $ encode (index i td) t') freshPVs
     pure $ HsCase t [(HsTupC freshPVs, HsConcat (toList factors))]
encode   (TVar i)       t = 
  do encoders <- envTerms
     pure $ HsApp (index i encoders) [t]
encode t@(TMu tds)      y = 
  do eTerm <- encoderTerm t
     pure $ HsApp eTerm [y] -- assumes the def of eTerm is generated elsewhere
encode t@(TApp f xs)    y = 
  do eTerm <- encoderTerm t
     pure $ HsApp eTerm [y] -- assumes the def of eTerm is generated elsewhere

||| Given a TDef t, gives a Haskell term of type Deserialiser [[ t ]]
||| where [[ t ]] is the interpretation of t as a type
decode : TDef n -> TermGen n HsTerm
decode    T0            = pure hsFailDecode
decode    T1            = pure $ hsReturn HsUnitTT
decode   (TSum {k} tds) = 
  do cases <- mapWithIndexA f tds
     [i] <- freshVars 1 "i"
     pure $ HsDo [ (Just i, hsReadInt (fromNat k))
                 , (Nothing, hsCaseDef i (toList cases) hsFailDecode)
                 ]
  where 
    injection : Fin l -> HsTerm -> HsTerm
    injection FZ x = hsLeft x
    injection {l = S (S Z)} (FS FZ) x = hsRight x
    injection (FS i) x = hsRight (injection i x)
    f : Fin (2 + k) -> TDef n -> TermGen n (HsTerm, HsTerm)
    f i t = 
      do t' <- assert_total $ decode t
         [y] <- freshVars 1 "y" -- TODO: could share this name between the branches
         pure (HsInt (finToInteger i), HsDo [(Just y, t'), (Nothing, hsReturn (injection i y))])
decode   (TProd {k} xs) = 
  do vs <- freshVars (2 + k) "x"
     xs' <- mapWithIndexA (\ i, x => map (MkPair (Just (index i vs))) $ assert_total (decode x)) xs
     pure (HsDo $ (toList xs') ++ [(Nothing, hsReturn (HsTupC vs))])
decode   (TVar i)       = 
  do decoders <- envTerms
     pure $ index i decoders
decode t@(TMu tds)      = decoderTerm t -- assumes the def of this is generated elsewhere
decode t@(TApp f xs)   = decoderTerm t -- assumes the def of this is generated elsewhere

||| Generate an encoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
encodeDef : TNamed n -> Haskell
encodeDef {n} t@(TName tname td) =
  let env = freshEnvWithTerms "encode"
      envTypes = map fst env
      funName = if tname == ""
                then encodeName (makeType envTypes td)
                else "encode" ++ uppercase tname
      varEncs = toList $ getUsedVars (map snd env) td
      currTerm = HsApp (HsFun funName) varEncs
      currType = if tname == ""
                 then makeType envTypes td
                 else HsParam tname []
      funType = foldr HsArrow (hsSerialiser (makeType' envTypes t)) (map hsSerialiser (getUsedVars envTypes td))
      clauses = genClauses n currType currTerm env varEncs td in
      FunDef funName funType clauses
  where 
    genConstructor : (n : Nat) -> String -> TDef n -> TermGen n (HsTerm, List HsTerm)
    genConstructor n name (TProd {k = k} xs) = 
      do xs' <- freshVars (2 + k) "x"
         rhs <- mapWithIndexA (\ i, t' => encode (index i xs) t') xs'
         pure $ (HsInn name (toList xs'), toList rhs)
    genConstructor n name td = 
      do [x'] <- freshVars 1 "x"
         rhs <- encode td x'
         pure $ (HsInn name [x'], [rhs])

    genClause : (n : Nat) -> List HsTerm -> Fin k -> (String, TDef n) -> TermGen n (List HsTerm, HsTerm)
    genClause n varEncs i (name, T1  ) = pure (varEncs ++ [HsInn name []], word (fromInteger (finToInteger i)))
    genClause n varEncs i (name, args) = 
      do (con, rhs) <- genConstructor n name args
         pure (varEncs ++ [con], simplify $ HsConcat (word (fromInteger (finToInteger i))::rhs))

        -- Idris is not clever enough to figure out the following type if written as a case expression
    genClauses : (n : Nat) -> HsType -> HsTerm -> Vect n (HsType, HsTerm) -> List HsTerm -> TDef n -> List (List HsTerm, HsTerm)
    genClauses n currType currTerm env varEncs (TMu [(name, td)]) = runTermGen ((currType, currTerm)::env) $ 
      do (con, rhs) <- genConstructor (S n) name td
         pure [(varEncs ++ [con], simplify $ HsConcat rhs)]
    genClauses n currType currTerm env varEncs (TMu tds) = 
      toList $ runTermGen ((currType, currTerm)::env) (mapWithIndexA (genClause (S n) varEncs) tds)
    genClauses n currType currTerm env varEncs td        = 
      let v = HsTermVar "x" in 
      [(varEncs ++ [v] , simplify $ runTermGen env (encode td v))]

||| Generate an decoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
decodeDef : TNamed n -> Haskell
decodeDef {n} t@(TName tname td) =
  let env = freshEnvWithTerms "decode"
      envTypes = map fst env
      funName = if tname == ""
                then decodeName (makeType envTypes td)
                else "decode" ++ uppercase tname
      varEncs = toList $ getUsedVars (map snd env) td
      currTerm = HsApp (HsFun funName) varEncs
      currType = if tname == ""  -- makeType' env t
                 then makeType envTypes td
                 else HsParam tname []
      funType = foldr HsArrow (hsDeserialiser (makeType' envTypes t)) (map hsDeserialiser (getUsedVars envTypes td))
      rhs = genCase n currType currTerm env td 
    in
  FunDef funName funType [(varEncs, rhs)]
  where 
    genConstructor : (n : Nat) -> String -> TDef n -> TermGen n (List (HsTerm, HsTerm))
    genConstructor n name (TProd {k = k} xs) = 
      do vs <- freshVars (2 + k) "x"
         xs' <- mapWithIndexA (\ i, x => do x' <- decode x
                                            pure (index i vs, x')) xs
         pure $ toList xs'
    genConstructor n name td = 
      do [v] <- freshVars 1 "x"
         xs' <- decode td
         pure $ [(v, xs')]

    genCases : (n : Nat) -> Fin k -> (String, TDef n) -> TermGen n (HsTerm, HsTerm)
    genCases n i (name, T1  ) = pure (HsInt (finToInteger i), hsReturn (HsInn name []))
    genCases n i (name, args) = 
      do args' <- genConstructor n name args
         pure (HsInt (finToInteger i), HsDo $ (map (\ (x, e) => (Just x, e)) args')++[(Nothing, hsReturn (HsInn name (map fst args')))])

    -- Idris is not clever enough to figure out the following type if written as a case expression
    genCase : (n : Nat) -> HsType -> HsTerm -> Vect n (HsType, HsTerm) -> TDef n -> HsTerm
    genCase n currType currTerm env (TMu [(name, td)]) = 
      simplify $ snd $ runTermGen ((currType, currTerm)::env) (genCases {k = S Z} (S n) FZ (name, td))
    genCase n currType currTerm env (TMu {k} tds)      = runTermGen ((currType, currTerm)::env) $ 
      do cases <- mapWithIndexA (genCases (S n)) tds
         [i] <- freshVars 1 "i"
         pure $ HsDo [ (Just i, hsReadInt (fromNat k))
                     , (Nothing, simplify $ hsCaseDef i (toList cases) hsFailDecode)
                     ]
    genCase n currType currTerm env td = simplify $ runTermGen env (decode td)

ASTGen Haskell HsType True where
  msgType  (Unbounded tn) = makeType' freshEnv tn
  generateTyDefs tns = 
    evalState (foldlM (\lh,(Unbounded tn) => (lh ++) <$> (makeDefs' tn)) [] tns) (the (List Name) [])
    --reverse $ evalState (makeDefs' tn) []
  generateTermDefs (Unbounded tn) =
 -- let deps = concatMap (\ (m**t) => [encodeDef t, decodeDef t]) (dependencies freshEnv (def tn)) in
 --     deps ++ 
        [encodeDef tn, decodeDef tn]

CodegenIndep Haskell HsType where
  typeSource = renderType
  defSource  = renderDef
  preamble   = text """import Data.Word
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
