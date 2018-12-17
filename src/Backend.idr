module Backend

import Data.Vect

import Types
import Typedefs

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


||| Vertically concatenate a list of documents with two newlines (i.e. one empty line) as separator.
vsep2 : List Doc -> Doc
vsep2 = vsep . punctuate line

||| Get the free names from the environment.
getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e)
  | (p ** v) = map (either id (const "")) v

||| Get a list of the de Brujin indices that are actually used in a TDef.
getUsedIndices : TDef n -> List (Fin n)
getUsedIndices T0 = []
getUsedIndices T1 = []
getUsedIndices (TSum xs) = assert_total $ concatMap getUsedIndices xs
getUsedIndices (TProd xs) = assert_total $ concatMap getUsedIndices xs
getUsedIndices (TVar i) = [i]
getUsedIndices (TMu nam xs) = assert_total $ concatMap ((concatMap weedOutZero) . getUsedIndices . snd) xs
  where weedOutZero : Fin (S n) -> List (Fin n)
        weedOutZero FZ = []
        weedOutZero (FS i) = [i]
getUsedIndices (TName nam t) = getUsedIndices t

||| Filter out the entries in an Env that is referred to by a TDef.
getUsedVars : Env n -> (td: TDef n) -> Env (length (getUsedIndices td))
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Interface for codegens. lang is a type representing (the syntactic structure of)
||| a type declaration in the target language.
interface Backend lang where
  ||| Given a TDef and a matching environment, generate a list of type definitions
  ||| in the target language.
  generateTyDefs : Env n -> TDef n -> List lang

  ||| Given a type definition in the target language, generate its code.
  generateCode : lang -> Doc

  ||| Generate a new environment with n free names.
  freshEnv : (n: Nat) -> Env n

||| Generate code in a specific language for a type definition and all its dependencies.
||| Needs to be called with the implicit parameter `lang`, as such: `generate {lang=Haskell} td`.
generate : Backend lang => {n: Nat} -> TDef n -> Doc
generate {lang} {n} td = vsep2 . map (generateCode) . generateTyDefs {lang=lang} (freshEnv {lang=lang} n) $ td

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
         traverseTD n (i, se) td = if td == weakenTDef (tdef se) _ (lteAddRight 0) then replace prf (TVar (fromNat (n + toNat i))) else go td
             where prf : m + n = n + m
                   prf = plusCommutative m n
                   go : TDef (n + m) -> TDef (n + m)
                   go T0 = T0
                   go T1 = T1
                   go (TSum xs) = TSum (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TProd xs) = TProd (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TMu nam xs) = TMu nam (assert_total $ map (\(c, t) => (c,traverseTD (S n) (i, se) t)) xs)
                   go (TName nam t) = TName nam (traverseTD n (i, se) t)
                   go x = x -- only TVar i case left
         td' : TDef (n + m)
         td' = foldl (flip (traverseTD n)) (weakenTDef td (n + m) (lteAddRight n)) (zip range table)
