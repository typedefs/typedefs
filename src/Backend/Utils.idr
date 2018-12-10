module Backend.Utils

import Typedefs
import Types

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export

-- TODO implementation in stdlib was erroneous, this has been merged but is not in a version yet. 
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

-- A purely syntactic parametric type declaration. (Type name plus parameters.)
-- Used in the standard type representing an environment.
-- TODO is number of parameters enough?
record Decl where
	constructor MkDecl
	name   : Name
	params : Vect n Name

-- Standard type for representing a variable environment.
-- Left=free, Right=bound.
Env : Nat -> Type
Env n = Vect n (Either Name Decl) -- TODO should Decl be a parameter?

-- Generate a new environment with n free names.
freshEnv : (n: Nat) -> Env n
freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

-- Get the free names from the environment.
getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e) 
  | (p ** v) = map (either id (const "")) v

-- 
vsep2 : List Doc -> Doc
vsep2 = vsep  . punctuate line

-- Interface for codegens. lang is a type representing (the syntactic structure of)
-- a type declaration in the target language.
interface Backend lang where
	-- Given a TDef and a matching environment, generate a list of type definitions
	-- in the target language.
  generateDefs : Env n -> TDef n -> List lang

  -- Given a type definition in the target language, generate its code.
  generateCode : lang -> Doc

-- Generate code in a specific language for a type definition and all its dependencies.
-- Needs to be called with {lang}
generate : Backend lang => {n: Nat} -> TDef n -> Doc
generate {lang} {n} td = vsep2 . map (generateCode) . generateDefs {lang=lang} (freshEnv n) $ td