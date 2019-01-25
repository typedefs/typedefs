module Backend

import Data.Vect

import Types
import Typedefs
import Backend.Utils

import Data.Vect
import Text.PrettyPrint.WL

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

||| Standard implmementation of `freshEnv` for languages that require type parameters to
||| start with lower case letters (and allow numbers in names).
freshEnvLC : (n : Nat) -> Env n
freshEnvLC n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

||| Standard implmementation of `freshEnv` for languages that require type parameters to
||| start with upper case letters (and allow numbers in names).
freshEnvUC : (n : Nat) -> Env n
freshEnvUC n = unindex {n} (\f => Left ("X" ++ show (finToInteger f)))

||| Get the free names from the environment.
getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e)
  | (p ** v) = map (either id (const "")) v

||| Get a list of the de Brujin indices that are actually used in a `TDef`.
getUsedIndices : TDef n -> List (Fin n)
getUsedIndices T0         = []
getUsedIndices T1         = []
getUsedIndices (TSum xs)  = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TProd xs) = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TVar i)   = [i]
getUsedIndices (TMu xs)   = assert_total $ nub $ concatMap ((concatMap weedOutZero) . getUsedIndices . snd) xs
  where weedOutZero : Fin (S n) -> List (Fin n)
        weedOutZero FZ     = []
        weedOutZero (FS i) = [i]
getUsedIndices (TApp f xs) = let fUses = assert_total $ getUsedIndices (td f)
                              in nub $ concatMap (assert_total getUsedIndices) $ map (flip index xs) fUses
--getUsedIndices (TName _ t) = getUsedIndices t

||| Filter out the entries in an `Env` that is referred to by a `TDef`.
getUsedVars : Env n -> (td: TDef n) -> Env (length (getUsedIndices td))
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Interface for codegens. `lang` is a type representing (the syntactic structure of)
||| a type declaration in the target language.
interface Backend lang where
  ||| Given a `TDef` and a matching environment, generate a list of type definitions
  ||| in the target language.
  generateTyDefs : Env n -> TDef n -> List lang

  ||| Given a type definition in the target language, generate its code.
  generateCode : lang -> Doc

  ||| Generate a new environment with n free names.
  freshEnv : (n: Nat) -> Env n

||| Use the given backend to generate code for a type definition and all its dependencies.
generate : (lang: Type) -> Backend lang => {n: Nat} -> TDef n -> Doc
generate lang {n} td = vsep2 . map (generateCode) . generateTyDefs {lang} (freshEnv {lang} n) $ td

||| Interface for codegens which distinguish between the message type itself and
||| its helper definitions. Currently doesn't support typedefs with free variables. 
interface NewBackend def type | def where
  ||| Given a `TDef`, generate its corresponding type signature.
  msgType  : TNamed 0 -> type

  ||| Given a `TDef`, generate a list of all helper definitions required by it.
  typedefs : TNamed n -> Vect n def -> List def

  ||| Given a type signature and a list of helper definitions which it uses,
  ||| generate source code.
  source   : type -> List def -> Doc

||| Use the given backend to generate code for a type definition and all its dependencies.
newGenerate : (lang: Type) -> NewBackend lang type => TNamed 0 -> Doc
newGenerate lang tn = source (msgType {def=lang} tn) (typedefs {def=lang} tn [])

record SpecialiseEntry where
  constructor MkSpecialiseEntry
  tdef : TDef 0
  ||| name of type used for specialisation
  targetType : String
  ||| name of function of target type generateType tdef -> targetType
  encodeFun : String
  ||| name of function of target type targetType -> generateType tdef
  decodeFun : String

||| Generate type definitions according to an *ordered* set of specialisation entries.
generateDefsSpecialised : Backend lang => Vect (S m') SpecialiseEntry -> (n : Nat) -> TDef n -> List lang
generateDefsSpecialised {lang} {m' = m'} table n td = generateTyDefs e td'
   where m : Nat
         m = S m'
         e : Env (n + m)
         e = freshEnv {lang} n ++ map (\ s => Right $ MkDecl (targetType s) []) table
         traverseTD : (n : Nat) -> (Fin m, SpecialiseEntry) -> TDef (n + m) -> TDef (n + m)
         traverseTD n (i, se) t = if t == weakenTDef (tdef se) _ (lteAddRight 0)
                                    then replace prf (TVar (fromNat (n + toNat i)))
                                    else go t
             where prf : m + n = n + m
                   prf = plusCommutative m n
                   go : TDef (n + m) -> TDef (n + m)
                   go T0 = T0
                   go T1 = T1
                   go (TSum xs)  = TSum (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TProd xs) = TProd (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TMu xs)   = TMu (assert_total $ map (\(c, t) => (c,traverseTD (S n) (i, se) t)) xs)
                   --go (TName name t) = TName name (traverseTD n (i, se) t)
                   go (TApp f xs) = ?goTApp
                   go x = x -- only TVar i case left
         td' : TDef (n + m)
         td' = foldl (flip (traverseTD n)) (weakenTDef td (n + m) (lteAddRight n)) (zip range table)
