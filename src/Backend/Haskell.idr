module Backend.Haskell

import Data.Vect
import Control.Monad.State

import Backend.Utils
import Backend

import Types
import Typedefs

%default partial
%access public export

guardPar : String -> String
guardPar str = if any isSpace $ unpack str then parens str else str

nameWithParams : Name -> Env n -> String
nameWithParams name e = withSep " " id (uppercase name::map lowercase (getFreeVars e))

makeType : Env n -> TDef n -> String
makeType     _ T0             = "Void"
makeType     _ T1             = "()"
makeType {n} e (TSum xs)      = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "Either " ++ guardPar (makeType e x) ++ " " ++ guardPar (makeType e y)
  tsum (x :: y :: z :: zs) = "Either " ++ guardPar (makeType e x) ++ " " ++ parens (tsum (y :: z :: zs))
makeType     e (TProd xs)     = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)       = either id id $ Vect.index v e
makeType     e (TMu name _)   = nameWithParams name e
makeType     e (TName name _) = nameWithParams name e

makeDefs : Env n -> TDef n -> State (List Name) String
makeDefs _ T0            = pure ""
makeDefs _ T1            = pure ""
makeDefs e (TProd xs)    = map concat $ traverse (makeDefs e) xs
makeDefs e (TSum xs)     = map concat $ traverse (makeDefs e) xs
makeDefs _ (TVar v)      = pure ""
makeDefs e (TMu name cs) = 
  do st <- get 
     if List.elem name st then pure "" 
      else let
         dataName = nameWithParams name e
         newEnv = Right (guardPar dataName) :: e
         args = withSep " | " (mkArg newEnv) cs
        in
       do res <- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
          put (name :: st)
          pure $ res ++ "\ndata " ++ dataName ++ " = " ++ args ++ "\n"
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg _ (cname, T1)       = cname
  mkArg e (cname, TProd xs) = cname ++ " " ++ withSep " " (makeType e) xs
  mkArg e (cname, ctype)    = cname ++ " " ++ makeType e ctype
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure "" 
       else 
        do res <- makeDefs e body 
           put (name :: st)
           pure $ res ++ "\ntype " ++ nameWithParams name e ++ " = " ++ makeType e body ++ "\n"

freshEnv : (n: Nat) -> Env n
freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

haskellBackend : Backend
haskellBackend =
 MkBackend (\ n => makeType)
           (\ n, e, td => evalState (makeDefs e td) [])
           freshEnv
