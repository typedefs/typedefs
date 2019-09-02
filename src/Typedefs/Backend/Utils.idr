module Typedefs.Backend.Utils

import Typedefs.Typedefs
import Typedefs.Backend.Specialisation
import Typedefs.Names

import Control.Monad.State
import Data.Vect
import Text.PrettyPrint.WL
import Data.SortedMap

import Effects
import Effect.State
import Effect.Exception

%default total
%access public export

||| A parametric type declaration (no definition, only name and parameters).
record Decl where
  constructor MkDecl

  ||| The name of the type.
  name   : Name

  ||| The names of the type's parameters.
  params : Vect n Name -- TODO is number of parameters enough?

||| A variable environment. Left=free, Right=bound.
Env : Nat -> Type
Env k = Vect k (Either String Decl)

||| Generate a fresh environment, using the supplied string as a prefix for variable names.
freshEnv : String -> Env n
freshEnv var = map (\ix => Left (var ++ show (finToInteger ix))) range

||| Get the free names from the environment.
getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e)
  | (p ** v) = map (either id (const "")) v


-- TODO implementation in base was erroneous, this has been merged but is not in a version yet.
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

||| Print a document with a width of 80 symbols.
print : Doc -> String
print = toString 1 80

||| Vertically concatenate a list of documents with two newlines (i.e. one empty line) as separator.
vsep2 : List Doc -> Doc
vsep2 = vsep . punctuate line

||| Produce a name for an anonymous `TMu` by simply concatenating its constructors.
nameMu : Vect n (Name, TDef' k a) -> Name
nameMu = concatMap (uppercase . fst)

||| "Flatten" all `TVar` references to `TMu`s into `TName`s named after the corresponding `TMu`, referencing `T0`s.
||| This is strictly meant to remove any `TVar`s from an AST.
||| The variable in the argument `TDef 1` is expected to reference the supplied name.
flattenMus : Name -> TDef' 1 b -> TDef' 0 b
flattenMus muName = flattenMu [muName]
  where
  -- DO NOT simply lift this function out to the top-level.
  -- Its behavior is dependent on the type of `makeDefs'`.
  -- (Specifically: all TVars must refer to a TMu, not to any free variables.)
  flattenMu : Vect (S n) Name -> TDef' (S n) a -> TDef' n a
  flattenMu names (TVar v)    = wrap $ TName (index v names) T0
  flattenMu _     T0          = T0
  flattenMu _     T1          = T1
  flattenMu names (TSum ts)   = assert_total $ TSum $ map (flattenMu names) ts
  flattenMu names (TProd ts)  = assert_total $ TProd $ map (flattenMu names) ts
  flattenMu names (TMu cs)    = assert_total $ TMu $ map (map (flattenMu ((nameMu cs) :: names))) cs
  flattenMu names (TApp f xs) = assert_total $ TApp f (map (flattenMu names) xs)
  flattenMu names (RRef i) {a = False} = wrap $ TName (index i names) T0
  flattenMu names (FRef i) {a = True } = FRef i

traverseEffect : (a -> Eff b e) -> Vect k a -> Eff (Vect k b) e
traverseEffect f [] = pure []
traverseEffect f (x :: xs) = do v <- f x
                                vs <- traverseEffect f xs
                                pure $ v :: vs

||| Errors that the compiler can throw
data CompilerError = RefNotFound String
                   | ReferencesNotSupported String

Show CompilerError where
  show (RefNotFound s) = "Could not find reference " ++ s
  show (ReferencesNotSupported s) = "References are not supported : " ++ s

Eq CompilerError where
  (RefNotFound s) == (RefNotFound s') = s == s'
  (ReferencesNotSupported s) == (ReferencesNotSupported s') = s == s'
  _ == _ = False

-- The state containing all the specialised types.
SPECIALIZED : Type -> EFFECT
SPECIALIZED targetType = 'Spec ::: STATE (SortedMap String targetType)

||| Errors that the compiler can throw.
ERR : EFFECT
ERR = EXCEPTION CompilerError

-- The state of already generated definitions
NAMES : EFFECT
NAMES = 'Names ::: STATE (List Name)

-- The context in which specialized type lookup is done
LookupM : Type -> Type -> Type
LookupM targetType t = Eff t [SPECIALIZED targetType, ERR]

runLookupM : Specialisation t => LookupM t a -> Either CompilerError a
runLookupM m = runInit ['Spec := specialisedTypes, default] m

-- The context in which definition are generated.
-- Keeps track of generated names and requires specialized types lookup
MakeDefM : Type -> Type -> Type
MakeDefM target t = Eff t [NAMES, SPECIALIZED target, ERR]

toEff : Either CompilerError a -> Eff a [ERR]
toEff (Left err) = raise err
toEff (Right val) = pure val

runMakeDefM : Specialisation t => MakeDefM t a -> Either CompilerError a
runMakeDefM m = runInit ['Names := [], 'Spec := specialisedTypes, default] m

-- idk why this is necessary sometimes
subLookup : LookupM target value -> MakeDefM target value
subLookup m = m

mapLeft : (a -> b) -> Either a k -> Either b k
mapLeft f (Left v) = Left (f v)
mapLeft f (Right v) = Right v

||| Only perform an action if a name is not already present in the state. If the action is performed, the name will be added.
ifNotPresent : {t : Type} -> Name -> MakeDefM t (List def) -> MakeDefM t (List def)
ifNotPresent n gen =
  if n `List.elem` !('Names :- get)
    then pure []
    else 'Names :- update (n ::) *> gen

extendContextEff : TDef n -> SortedMap String b -> Vect n b
               -> Eff (k ** (TDefR (n + k), Vect (n + k) b)) [ERR]
extendContextEff td m v = Utils.toEff $ mapLeft RefNotFound $ extendContext td m v
