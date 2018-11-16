module Backend.ReasonML

import Data.Vect
import Control.Monad.State

import Backend.Utils
import Types
import Typedefs

%default partial
%access public export

formatVar : String -> String
formatVar = (strCons '\'') . lowercase

makeType : Env n -> TDef n -> String
makeType     _ T0            = "void"
makeType     _ T1            = "unit"
makeType {n} e (TSum xs)     = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "either" ++ (parens $ (makeType e x) ++ ", " ++ makeType e y)
  tsum (x :: y :: z :: zs) = "either" ++ (parens $ (makeType e x) ++ ", " ++ tsum (y :: z :: zs))
makeType     e (TProd xs)    = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)      = either formatVar lowercase $ Vect.index v e
makeType     e (TMu name _)   = lowercase name ++ parens (withSep ", " id (getFreeVars e formatVar))
makeType     _ (TName name _) = lowercase name

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
         dataName = name ++ (parens $ withSep ", " id (getFreeVars e formatVar))
         newEnv = Right dataName :: e
         args = withSep " | " (mkArg newEnv) cs
        in
       do res <- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
          put (name :: st)
          pure $ res ++ "\ntype " ++ lowercase dataName ++ " = " ++ args ++ ";\n"
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg _ (cname, T1)       = cname
  mkArg e (cname, TProd xs) = uppercase cname ++ parens (withSep ", " (makeType e) xs)
  mkArg e (cname, ctype)    = uppercase cname ++ parens (makeType e ctype)
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure "" 
       else let 
          typeName = lowercase name ++ (parens $ withSep ", " id (getFreeVars e formatVar))
         in
        do res <- makeDefs e body 
           put (name :: st)
           pure $ res ++ "\ntype " ++ typeName ++ " = " ++ makeType e body ++ ";\n"
  

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> String
generateType {n} = makeType (freshEnv n)

-- generate data definitions
generate : TDef n -> String
generate {n} td = evalState (makeDefs (freshEnv n) td) []      

-- type definitions to be included in all outputs
helperTypes : String
helperTypes = "type void;\n\ntype either('a,'b) = Left('a) | Right('b);\n"