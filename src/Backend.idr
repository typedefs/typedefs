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

record SpecialiseEntry where
  constructor MkSpecialiseEntry
  tdef : TDef 0
  ||| name of type used for specialisation
  targetType : String
  ||| name of function of target type generateType tdef -> targetType
  encodeFun : String
  ||| name of function of target type targetType -> generateType tdef
  decodeFun : String

generateDefsSpecialised : Backend -> Vect (S m') SpecialiseEntry -> (n : Nat) -> TDef n -> String
generateDefsSpecialised {m' = m'} be table n td = generateDefsEnv be (n + m) e td'
   where m : Nat
         m = S m'
         e : Env (n + m)
         e = freshEnv be n ++ map (\ s => Right $ targetType s) table
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
