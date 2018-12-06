module Backend

import Data.Vect

import Types
import Typedefs

%default total
%access public export

Env : Nat -> Type
Env k = Vect k (Either String String) -- left=free / right=bound

getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e)
  | (p ** v) = map (either id (const "")) v



record Backend where
  constructor MkBackend
  ||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
  generateTypeEnv : (n : Nat) -> Env n -> TDef n -> String
  ||| Generate data definitions
  generateDefsEnv : (n : Nat) -> Env n -> TDef n -> String
  freshEnv : (n : Nat) -> Env n

generateType : Backend -> (n : Nat) -> TDef n -> String
generateType be n td = generateTypeEnv be n (freshEnv be n) td

generateDefs : Backend -> (n : Nat) -> TDef n -> String
generateDefs be n td = generateDefsEnv be n (freshEnv be n) td
