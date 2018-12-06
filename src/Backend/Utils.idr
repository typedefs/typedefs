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

Src : Type -> Type
Src lang = Doc

interface Backend lang where
--  generateDefs : Env decl n -> TDef n -> List def
--  generateCode : def -> Src def
  generate : TDef n -> Src lang


--generate : Backend b d => {n: Nat} -> TDef n -> Src b
--generate {n} td = vsep2 . map generateCode . generateDefs (freshEnv n) $ td