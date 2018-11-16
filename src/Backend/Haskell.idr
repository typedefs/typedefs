module Backend.Haskell

import Data.Vect
import Control.Monad.State

import Backend.Utils
import Types
import Typedefs

%default partial
%access public export

guardPar : String -> String
guardPar str = if any isSpace $ unpack str then parens str else str

makeType : Env n -> TDef n -> String
makeType     _ T0            = "Void"
makeType     _ T1            = "()"
makeType {n} e (TSum xs)     = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "Either " ++ guardPar (makeType e x) ++ " " ++ guardPar (makeType e y)
  tsum (x :: y :: z :: zs) = "Either " ++ guardPar (makeType e x) ++ " " ++ parens (tsum (y :: z :: zs))
makeType     e (TProd xs)    = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)      = either id id $ Vect.index v e
makeType     e (TMu name _)   = withSep " " id (uppercase name::getFreeVars e lowercase)
makeType     _ (TName name _) = name

makeDefs : Env n -> TDef n -> State (List Name) String
makeDefs _ T0           = pure ""
makeDefs _ T1           = pure ""
makeDefs e (TProd xs)   = map concat $ traverse (makeDefs e) xs
makeDefs e (TSum xs)    = map concat $ traverse (makeDefs e) xs
makeDefs _ (TVar v)     = pure ""
makeDefs e (TMu name cs) = 
  do st <- get 
     if List.elem name st then pure "" 
      else let
         dataName = withSep " " id (uppercase name::getFreeVars e lowercase)
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
       else let 
          typeName = withSep " " id (uppercase name::getFreeVars e lowercase)
         in
        do res <- makeDefs e body 
           put (name :: st)
           pure $ res ++ "\ntype " ++ typeName ++ " = " ++ makeType e body ++ "\n"

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> String
generateType {n} = makeType (freshEnv n)

-- generate data definitions
generate : TDef n -> String
generate {n} td = evalState (makeDefs (freshEnv n) td) []