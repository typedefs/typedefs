module Backend.Utils

import Typedefs
import Types

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export

-- TODO implementation in base was erroneous, this has been merged but is not in a version yet. 
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

||| A parametric type declaration (no definition, only name and parameters).
record Decl where
  constructor MkDecl

  ||| The name of the type.
  name   : Name

  ||| The names of the type's parameters.
  params : Vect n Name -- TODO is number of parameters enough?

||| A variable environment. Left=free, Right=bound.
Env : Nat -> Type
Env n = Vect n (Either Name Decl) -- TODO should Decl be a parameter?

||| Get the free names from the environment.
getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e) 
  | (p ** v) = map (either id (const "")) v

||| Vertically concatenate a list of documents with two newlines (i.e. one empty line) as separator.
vsep2 : List Doc -> Doc
vsep2 = vsep . punctuate line

||| Print a document with a width of 80 symbols.
print : Doc -> String
print = toString 1 80

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

||| Standard implmementation of `freshEnv` for languages that require type parameters to
||| start with lower case letters (and allow numbers in names).
freshEnvLC : (n : Nat) -> Env n
freshEnvLC n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

||| Standard implmementation of `freshEnv` for languages that require type parameters to
||| start with upper case letters (and allow numbers in names).
freshEnvUC : (n : Nat) -> Env n
freshEnvUC n = unindex {n} (\f => Left ("X" ++ show (finToInteger f)))