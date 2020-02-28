module Typedefs.Backend.Purescript

import Typedefs.Names
import Typedefs.Typedefs

import Typedefs.Backend
import Typedefs.Backend.Specialisation
import Typedefs.Backend.Utils

import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect
import Data.NEList
import Data.SortedMap

import Effects
import Effect.State
import Effect.Exception

%default total
%access export

-- Representing Purescript source code -----

||| The syntactic structure of Purescript types.
public export
data PsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  PsVoid  :                                PsType

  ||| The `()` (i.e. unit/singleton) type.
  PsUnit  :                                PsType

  ||| The tuple type, containing two or more further types.
  PsTuple :         Vect (2 + n) PsType -> PsType

  ||| The sum type, containing two further types.
  PsSum   :         PsType -> PsType    -> PsType

  ||| A type variable.
  PsVar   :         Name                -> PsType

  ||| A named type with zero or more other types as parameters.
  PsParam : Name -> Vect n PsType       -> PsType

  ||| A function type (only used for top-level type of termdef
  ||| decoders and encoders)
  PsArrow :         PsType -> PsType    -> PsType

printType : PsType -> String
printType PsVoid = "Void"
printType PsUnit = "()"
printType (PsTuple xs) = "(" ++ concat (intersperse " /\\ " (map (assert_total printType) xs)) ++ ")"
printType (PsSum x y) = "(Either " ++ printType x ++ printType y ++ ")"
printType (PsVar x) = x
printType (PsParam x xs) = x ++ concat (intersperse " " (map (assert_total printType) xs))
printType (PsArrow x y) = printType x ++ " -> " ++ printType y

public export
Show PsType where
  show = printType

public export
Eq PsType where
  PsVoid == PsVoid = True
  PsUnit == PsUnit = True
  (PsTuple l {n = nl} ) == (PsTuple r {n = nr}) with (decEq nl nr)
    (PsTuple l {n = nl} ) == (PsTuple r {n = nl}) | Yes Refl = assert_total $ l == r
    (PsTuple l {n = nl} ) == (PsTuple r {n = nr}) | No _ = False
  (PsSum xl yl)  == (PsSum xr yr)  = xl == xr && yl == yr
  (PsVar l) == (PsVar r) = l == r
  (PsParam xl yl {n = nl}) == (PsParam xr yr {n = nr}) with (decEq nl nr)
    (PsParam xl yl {n = nl}) == (PsParam xr yr {n = nl}) | Yes Refl =
      assert_total $ xl == xr && yl == yr
    (PsParam xl yl {n = nl}) == (PsParam xr yr {n = nr}) | No _ = False
  (PsArrow xl yl) == (PsArrow xr yr) = xl == xr && yl == yr
  _ == _ = False

psNamed : String -> PsType
psNamed = flip PsParam []

private
psParam : Decl -> PsType
psParam (MkDecl n ps) = PsParam n (map PsVar ps)

||| The syntactic structure of (a subset of) Purescript terms.
data PsTerm : Type where
  ||| The unit term `()`.
  PsUnitTT  :                                         PsTerm

  ||| The tuple constructor, containing two or more further terms.
  PsTupC :            Vect (2 + n) PsTerm          -> PsTerm

  ||| A term variable, with a name (no need for deBruijn indices when terms are first-order!).
  PsTermVar : Name                                 -> PsTerm

  ||| The wildcard pattern `_`.
  PsWildcard  :                                       PsTerm

  ||| A data type constructor, containing a name and a list of further terms.
  PsInn :     Name -> List PsTerm                  -> PsTerm

  ||| A case expression, containing a term being examined, and a list
  ||| of (lhs, rhs) pairs. Invariants: lhs is a pattern (ie all
  ||| variables occur linearly), and FreeVars(rhs) \subseteq
  ||| FreeVars(lhs).
  PsCase : PsTerm ->  List (PsTerm, PsTerm)       -> PsTerm

  ||| A function application.
  PsApp : PsTerm   -> List PsTerm                 -> PsTerm

  ||| (The name of) a function.
  PsFun : Name                                    -> PsTerm

  ||| Do-notation: A list of statements of the form
  |||   x <- e    [ represented by (Just x, e)
  ||| or simply
  |||   e         [ represented by (Nothing, e)].
  PsDo :              List (Maybe PsTerm, PsTerm) -> PsTerm

  -- special constants (for convencience)

  ||| A Word8 converted from an Int literal (`fromIntegral i`).
  PsWord8 : Int                                   -> PsTerm

  ||| An Int literal.
  PsInt : Integer                                 -> PsTerm

  ||| `mconcat :: [Builder] -> Builder` from Data.ByteString.Builder.
  PsConcat :          List PsTerm                 -> PsTerm

||| The syntactic structure of Purescript type declarations.
data Purescript : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> PsType                -> Purescript

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Purescript type.
  ADT     : Decl -> Vect n (Name, PsType) -> Purescript

  ||| A function definition is a declared name, a type, and a list of
  ||| clauses of the form ((arg1, ..., argk), rhs).
  FunDef : Name -> PsType -> List (List PsTerm, PsTerm) -> Purescript

specialisedMap : SortedMap String (PsType, PsTerm)
specialisedMap = foldr {t=List} (uncurry insert) empty $
                 [ ("Int"  , (psNamed "Int"  , PsUnitTT))
                 , ("Bool" , (psNamed "Bool" , PsUnitTT))
                 , ("Maybe", (psNamed "Maybe", PsUnitTT))
                 , ("List" , (psNamed "List" , PsUnitTT))
                 ]

Specialisation (PsType, PsTerm) where
  specialisedTypes = specialisedMap

-- Effects -----

||| Environment, contains currently used variables and names
ENV : Nat -> EFFECT
ENV n = 'Env ::: STATE (SortedMap String Nat, Vect n (PsType, PsTerm))

||| Monad for the term generator, keeping track of a name supply (in
||| the form of a map of the number of usages for each name) and a
||| "semantic" environment consisting of an environment of types, and
||| terms for decoding/encoding the types.
||| @ n the size of the environment
TermGen : (n : Nat) -> Type -> Type
TermGen n t = Eff t [ENV n, SPECIALIZED (PsType, PsTerm), ERR]

toTermGen : Either CompilerError a -> TermGen n a
toTermGen (Left err) = raise err
toTermGen (Right val) = pure val

runTermGen : (env : Vect n (PsType, PsTerm)) -> TermGen n a -> Either CompilerError a
runTermGen env mx = runInit (initialState env) mx
  where -- For some reason, inlining this definition will make type inference confused and infer that as
    -- `Env eff […]` instead of `Env (Either CompilerError) […]`
    initialState : (env : Vect n (PsType, PsTerm)) -> Env (Either CompilerError)
      [ STATE (LRes 'Env (SortedMap String Nat, Vect n (PsType, PsTerm)))
      , STATE (LRes 'Spec (SortedMap String (PsType, PsTerm)))
      , EXCEPTION CompilerError
      ]
    initialState env = ['Env := (empty, env), 'Spec := specialisedTypes, default]

PurescriptDefM : Type -> Type
PurescriptDefM = MakeDefM (PsType, PsTerm)

-- TODO use definition from Utils
-- The state monad in which name lookup happens, contains a sorted map of existing types, can throw errors
PurescriptLookupM : Type -> Type
PurescriptLookupM = LookupM (PsType, PsTerm)

toPurescriptLookupM : Either CompilerError a -> PurescriptLookupM a
toPurescriptLookupM (Left err) = raise err
toPurescriptLookupM (Right val) = pure val

-- Execute the lookup monad, any error will result in a `Left` value.
runPurescriptLookupM : PurescriptLookupM a -> Either CompilerError a
runPurescriptLookupM = runLookupM

subEffect :  (Eff a es -> Either CompilerError a) -> Eff a es -> TermGen n a
subEffect run eff= toTermGen $ run eff

-- Rendering Purescript source code -----

||| Render a name applied to a list of arguments exactly as written.
||| Arguments need to be previously parenthesized, if applicable.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

psTupled : List Doc -> Doc
psTupled = encloseSep empty empty (text "/\\")

mutual
  ||| Render a type signature as Purescript source code.
  renderType : PsType -> Doc
  renderType PsVoid                = text "Void"
  renderType PsUnit                = text "()"
  renderType (PsTuple xs)          = psTupled . toList . map (assert_total renderType) $ xs
  renderType (PsSum a b)           = renderApp "Either" [guardParen a, guardParen b]
  renderType (PsVar v)             = text (lowercase v)
  renderType (PsParam name params) = renderApp name (map guardParen params)
  renderType (PsArrow a b)         = renderArrow (renderParamNoParen a) b
    where
      -- Parenthesize, except for Param (since e.g. type application binds stronger than ->)
      renderParamNoParen : PsType -> Doc
      renderParamNoParen a@(PsParam _ _) = renderType a
      renderParamNoParen a               = guardParen a

      renderArrow : Doc -> PsType -> Doc
      renderArrow a (PsArrow b' c') = a |++| text "->" |++| (renderArrow (renderParamNoParen b') c')
      renderArrow a b               = a |++| text "->" |++| (renderParamNoParen b)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : PsType -> Doc
  guardParen t@(PsParam _ []) = assert_total $ renderType t
  guardParen t@(PsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t@(PsSum _ _ )   = parens (assert_total $ renderType t)
  guardParen t@(PsArrow _ _)  = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

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
||| - In do blocks: `(pure a) >>= f` ~> f a
||| - mconcat [] ~> mempty
||| - mconcat [a] ~> a
||| - mconcat (xs ++ [mempty] ++ ys) ~> mconcat (xs ++ ys)
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
        -- replace "x <- pure a; e" by "e[a/x]"
        -- assumes the free variables in a are not bound in e
        (Just (PsTermVar x), PsApp (PsFun "pure") [a]) =>
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
private
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
private
freshEnvWithTerms : (prefix : String) -> Vect n (PsType, PsTerm)
freshEnvWithTerms prefix = map (\ x => (x, PsTermVar (prefix ++ uppercase (psTypeName x)))) freshEnv

||| Generate a Purescript type from a `TDef`.
makeType : Vect n PsType -> TDefR n -> PurescriptLookupM PsType
makeType _    T0          = pure PsVoid
makeType _    T1          = pure PsUnit
makeType e    (TSum xs)   = do ys <- traverseEffect (assert_total $ makeType e) xs
                               pure $ foldr1' PsSum ys
makeType e    (TProd xs)  = do ys <- traverseEffect (assert_total $ makeType e) xs
                               pure $ PsTuple ys
makeType e    (TVar v)    = pure $ Vect.index v e
makeType e td@(TMu cases) = pure $ PsParam (nameMu cases) $ getUsedVars e td
makeType e    (TApp f xs) = do ys <- (traverseEffect (assert_total (makeType e)) xs)
                               pure $ PsParam (name f) ys
makeType e    (RRef i)    = pure $ Vect.index i e
                            --do specMap <- 'Spec :- get
                            --   case lookup n specMap of
                            --     Just t => pure t
                            --     Nothing => raise $ RefNotFound ("could not find " ++ n ++ " in " ++ (show $ keys specMap))

||| Generate a Purescript type from a `TNamed`.
makeType' : Vect n PsType -> TNamedR n -> PurescriptLookupM PsType
makeType' e (TName ""   body) = makeType e body --escape hatch; used e.g. for all non-TApp dependencies of a TApp
makeType' e (TName name body) = pure $ PsParam name $ getUsedVars e body

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
  makeTypeFromCase env (name, def) = pure (name, !(makeType env def))

  ||| Generate Purescript type definitions for a `TNamed` and all of its dependencies.
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
                type <- (makeType freshEnv body)
                pure $ res ++ [Synonym decl type]

-- Convenience definitions for Termdefs -----

-- `absurd :: Void -> a` from Data.Void
private
psAbsurd : PsTerm -> PsTerm
psAbsurd t = PsApp (PsFun "absurd") [t]

-- `mempty :: Builder` from Data.ByteString.Builder
private
psEmpty : PsTerm
psEmpty = PsFun "mempty"

-- `Deserialiser` type family
private
psDeserialiser : PsType -> PsType
psDeserialiser a = PsParam "Deserialiser" [a]

-- `Serialiser` type family
private
psSerialiser : PsType -> PsType
psSerialiser a = PsParam "Serialiser" [a]

-- `deserialiseInt :: Deserialiser Integer`
-- @k how many bits should be read (currently ignored)
private
psReadInt : Integer -> PsTerm
psReadInt k = PsApp (PsFun "deserialiseInt") [] -- [PsInt k]

-- `failDecode :: Deserialiser a`
private
psFailDecode : PsTerm
psFailDecode = PsFun "failDecode"

-- `pure :: a -> Deserialiser a`
private
psPure : PsTerm -> PsTerm
psPure x = PsApp (PsFun "pure") [x]

-- `Left : a -> Either a b`
private
psLeft : PsTerm -> PsTerm
psLeft x = PsInn "Left" [x]

-- `Right : b -> Either a b`
private
psRight : PsTerm -> PsTerm
psRight x = PsInn "Right" [x]

-- `case t of cases; _ -> def`
private
psCaseDef : PsTerm -> List (PsTerm, PsTerm) -> PsTerm -> PsTerm
psCaseDef t cases def = PsCase t (cases ++ [(PsWildcard, def)])

-- `word8 :: Word8 -> Builder` from Data.ByteString.Builder
private
word : Int -> PsTerm
word i = PsApp (PsFun "word8") [PsWord8 i]


traverseWithIndex : (Fin n -> a -> TermGen m b) -> Vect n a -> TermGen m (Vect n b)
traverseWithIndex f []        = pure []
traverseWithIndex f (x :: xs) = do y <- f FZ x
                                   ys <- traverseWithIndex (f . FS) xs
                                   pure (y :: ys)

||| Given an environment, run the term generator, with no names
||| already used to start with.
|||| @ env environment to use

||| Extract an environment of types.
envTypes : TermGen n (Vect n PsType)
envTypes = do (_, fs) <- 'Env :- get
              pure $ map fst fs

||| Extract an environment of encoder/decoder terms.
envTerms : TermGen n (Vect n PsTerm)
envTerms = do (_, fs) <- 'Env :- get
              pure $ map snd fs

||| Generate a vector of fresh variables, using a given string as a
||| name suggestion.
||| @ k number of variables to generate
||| @ suggestion name to use if possible
freshVars : (k : Nat) -> (suggestion : String) -> TermGen n (Vect k PsTerm)
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
encodeName : PsType -> Name
encodeName ty = "encode" ++ (uppercase $ psTypeName ty)

||| Name to use for decoder at this type.
decodeName : PsType -> Name
decodeName ty = "decode" ++ (uppercase $ psTypeName ty)

||| Term to use for encoder/decoder for the given `TDef`.
||| @ namer should be either `encodeName` or `decodeName`; determines if
|||         we generate the encoder or decoder term.
encoderDecoderTerm : (namer : PsType -> Name) -> TDefR n -> TermGen n PsTerm
encoderDecoderTerm namer (TApp g xs) =
  do xs' <- traverseEffect (assert_total $ encoderDecoderTerm namer) xs
     pure (PsApp (PsFun (namer (PsParam (name g) []))) (toList xs'))
encoderDecoderTerm namer (TVar i)    = index i <$> envTerms
encoderDecoderTerm namer td          =
  do env <- envTerms
     let varEncoders = getUsedVars env td
     rawType <- makeType freshEnv td
     pure $ PsApp (PsFun (namer rawType)) (toList varEncoders)

||| Term to use for encoder for this `TDef`.
encoderTerm : TDefR n -> TermGen n PsTerm
encoderTerm td = encoderDecoderTerm encodeName td

||| Term to use for encoder for this `TDef`.
decoderTerm : TDefR n -> TermGen n PsTerm
decoderTerm td = encoderDecoderTerm decodeName td

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
    goMu env tds = do muType <- makeType env (TMu tds)
                      let tdefs = map snd tds
                      let extendedEnv = muType :: env
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
        envxs <- traverseEffect (makeType env) xs
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
encode : (td : TDefR n) -> (t : PsTerm) -> TermGen n PsTerm
encode    T0            t = pure (psAbsurd t)
encode    T1            t = pure psEmpty
encode   (TSum td)      t =
  do summands <- injectionInv td
     pure $ PsCase t (map (\ (lhs, i, rhs) => (lhs, PsConcat [word i, rhs])) summands)
  where
    injectionInv : Vect (2 + k) (TDefR n) -> TermGen n (List (PsTerm, Int, PsTerm))
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
decode : TDefR n -> TermGen n PsTerm
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
    injection FZ x = psLeft x
    injection {l = S (S Z)} (FS FZ) x = psRight x
    injection (FS i) x = psRight (injection i x)
    f : Fin (2 + k) -> TDefR n -> TermGen n (PsTerm, PsTerm)
    f i t =
      do t' <- assert_total $ decode t
         [y] <- freshVars 1 "y" -- TODO: could share this name between the branches
         pure (PsInt (finToInteger i), PsDo [(Just y, t'), (Nothing, psPure (injection i y))])
decode   (TProd {k} xs) =
  do vs <- freshVars (2 + k) "x"
     xs' <- traverseWithIndex (traverseIndexDecode vs) xs
     pure (PsDo $ (toList xs') ++ [(Nothing, psPure (PsTupC vs))])
  where
    traverseIndexDecode : Vect (2 + k) PsTerm -> Fin (2 + k) -> TDefR n -> TermGen n (Maybe PsTerm, PsTerm)
    traverseIndexDecode vars i tdef = pure (Just $ index i vars, !(assert_total $ decode tdef))
decode   (TVar i)       = pure $ index i !envTerms
decode t@(TMu tds)      = decoderTerm t -- assumes the def of this is generated elsewhere
decode t@(TApp f xs)    = decoderTerm t -- assumes the def of this is generated elsewhere
decode   (RRef i)       = pure $ index i !envTerms

||| Generate an encoder function definition for the given TNamed.
||| Assumes definitions it depends on are generated elsewhere.
encodeDef : TNamedR n -> PurescriptLookupM Purescript
encodeDef {n} t@(TName tname td) = do
      let env = freshEnvWithTerms "encode"
      let envTypes = map fst env
      funName <- if tname == ""
                    then encodeName <$> makeType envTypes td
                    else pure $ "encode" ++ uppercase tname
      let varEncs = toList $ getUsedVars (map snd env) td
      currTerm <- pure $ PsApp (PsFun funName) varEncs
      currType <- if tname == ""
                     then makeType envTypes td
                     else pure $ PsParam tname []
      funType <- do init <- makeType' envTypes t
                    pure $ foldr PsArrow
                                (psSerialiser init)
                                (map psSerialiser (getUsedVars envTypes td))
      clauses <- toPurescriptLookupM $ genClauses n currType currTerm env varEncs td
      pure $ FunDef funName funType clauses
  where
    genConstructor : (n : Nat) -> String -> TDefR n -> TermGen n (PsTerm, List PsTerm)
    genConstructor n name (TProd {k = k} xs) =
      do xs' <- freshVars (2 + k) "x"
         rhs <- traverseWithIndex (\ i, t' => encode (index i xs) t') xs'
         pure $ (PsInn name (toList xs'), toList rhs)
    genConstructor n name td =
      do [x'] <- freshVars 1 "x"
         rhs <- encode td x'
         pure $ (PsInn name [x'], [rhs])

    genClause : (n : Nat) -> List PsTerm -> Fin k -> (String, TDefR n) -> TermGen n (List PsTerm, PsTerm)
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
  do let env = freshEnvWithTerms "decode"
     let envTypes = map fst env
     funName <- if tname == ""
                   then decodeName <$> makeType envTypes td
                   else pure $ "decode" ++ uppercase tname
     let varEncs = toList $ getUsedVars (map snd env) td
     let currTerm = PsApp (PsFun funName) varEncs
     currType <- if tname == ""  -- makeType' env t
                    then makeType envTypes td
                    else pure $ PsParam tname []
     funType <- do init <- makeType' envTypes t
                   pure $ foldr PsArrow
                                (psDeserialiser init)
                                (map psDeserialiser (getUsedVars envTypes td))
     rhs <- genCase n currType currTerm env td
     pure $ FunDef funName funType [(varEncs, rhs)]
  where
    genConstructor : (n : Nat) -> String -> TDefR n -> TermGen n (List (PsTerm, PsTerm))
    genConstructor n name (TProd {k = k} xs) =
      do vs <- freshVars (2 + k) "x"
         xs' <- traverseWithIndex (\ i, x => pure (index i vs, !(decode x))) xs
         pure $ toList xs'
    genConstructor n name td =
      do [v] <- freshVars 1 "x"
         xs' <- decode td
         pure $ [(v, xs')]

    genCases : (n : Nat) -> Fin k -> (String, TDefR n) -> TermGen n (PsTerm, PsTerm)
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
  msgType  (Unbounded tn) = runPurescriptLookupM $ makeType' freshEnv tn
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
