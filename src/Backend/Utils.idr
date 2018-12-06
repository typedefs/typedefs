module Backend.Utils

import Typedefs
import Types

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export



-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

-- Custom foldr1 because the standard one doesn't handle base case correctly.
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))


--freshEnv : (n: Nat) -> Env n
--freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

withSep : String -> (a -> String) -> Vect k a -> String
withSep sep fn xs = concat $ intersperse sep $ map fn xs

data Decl : Type where
  MkDecl : Name -> Vect n Name -> Decl

Env : Nat -> Type
Env n = Vect n (Either Name Decl) -- TODO should Decl be a parameter?

getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e) 
  | (p ** v) = map (either id (const "")) v

vsep2 : List Doc -> Doc
vsep2 = vsep  . punctuate line


freshEnv : (n : Nat) -> Env n
freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

interface Backend lang where
  generateDefs : Env n -> TDef n -> List lang
  generateCode : lang -> Doc

-- Needs to be called with {lang}
generate : Backend lang => {n: Nat} -> TDef n -> Doc
generate {lang} {n} td = vsep2 . map (generateCode) . generateDefs {lang=lang} (freshEnv n) $ td