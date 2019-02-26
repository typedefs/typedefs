module Backend

import Data.Vect

import Types
import Typedefs
import Backend.Utils

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export

{-
||| Interface for codegens. `lang` is a type representing (the syntactic structure of)
||| a type declaration in the target language.
interface Backend lang where
  ||| Given a `TDef` and a matching environment, generate a list of type definitions
  ||| in the target language.
  generateTyDefs : Env n -> TNamed n -> List lang

  ||| Given a type definition in the target language, generate its code.
  generateCode : lang -> Doc

  ||| Generate a new environment with n free names.
  freshEnv : (n: Nat) -> Env n

||| Use the given backend to generate code for a type definition and all its dependencies.
generate : (lang: Type) -> Backend lang => {n: Nat} -> TNamed n -> Doc
generate lang {n} td = vsep2 . map (generateCode) . generateTyDefs {lang} (freshEnv {lang} n) $ td
-}

||| Interface for interpreting type definitions as ASTs.
||| @def  the type representing type definitions.
||| @type the type representing type signatures.
||| @n    the number of variables the interpretor supports in a type definition. (Should always be either `n` or `0`.)
interface AST def type (n : Nat) | def where
  ||| Given a `TDef`, generate its corresponding type signature.
  msgType  : TNamed n -> type

  ||| Generate definitions for a `TNamed` and all its helper definitions.
  generateTyDefs : TNamed n -> List def

||| Interface for code generators that can generate code for type definitions and
||| type signatures independently of each other.
||| @def  the type representing type definitions.
||| @type the type representing type signatures.
interface CodegenIndep def type | def where
  ||| Generate source code for a type signature.
  typeSource : type -> Doc

  ||| Generate source code for a type definition.
  defSource : def -> Doc

||| Use the given backend to generate code for a type definition and all its dependencies.
generateDefs : (def: Type) -> AST def type n => CodegenIndep def type => TNamed n -> Doc
generateDefs def tn = vsep2 $ map defSource (generateTyDefs {def} tn)

||| Use the given backend to generate code for a type signature.
generateType : (def: Type) -> AST def type n => CodegenIndep def type => TNamed n -> Doc
generateType def tn = typeSource {def} (msgType {def} tn)

||| Interface for code generators that need to generate code for type definitions and
||| type signatures at the same time.
||| @def  the type representing type definitions.
||| @type the type representing type signatures.
interface CodegenInterdep def type where
  ||| Generate source code for a type signature and a list of helper definitions.
  sourceCode   : type -> List def -> Doc

||| Use the given backend to generate code for a type definition and all its dependencies.
generate : (def: Type) -> AST def type n => CodegenInterdep def type => TNamed n -> Doc
generate def tn = sourceCode (msgType {def} tn) (generateTyDefs {def} tn)


--generate : (lang: Type) -> Backend lang type n => TNamed n -> Doc
--generate lang tn = sourceCode ?hmm (generateTyDefs {def=lang} tn)

--||| Interface for codegens which support code generation of open type definitions.
--interface Backend def type => OpenBackend def where
--  ||| Generate definitions for a `TNamed` and all its helper definitions.
--  generateOpenTyDefs : TNamed n -> List def

{-
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
-}