module Backend.ReasonML

import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default partial
%access public export

data RMLType : Type where
  H0 : RMLType
  H1 : RMLType
  HProd : Vect (2 + k) RMLType -> RMLType
  HVar : Name -> RMLType
  HParam : Name -> RMLType -> RMLType

data RMLDef : Type where
  Synonym : Name -> Vect n Name -> RMLType -> RMLDef
  ADT     : Name -> Vect n Name -> Vect k (Name, RMLType) -> RMLDef

formatVar : String -> String
formatVar = (strCons '\'') . lowercase

nameWithParams : Name -> Env n -> String
nameWithParams name e = lowercase name ++ (withSep ", " formatVar (getFreeVars e))

typeName : Name -> List Name -> String
typeName name [] = lowercase name
typeName name ps = lowercase name ++ parens (concat $ intersperse ", " $ map formatVar ps) 

makeType : Env n -> TDef n -> String
makeType     _ T0             = "void"
makeType     _ T1             = "unit"
makeType {n} e (TSum xs)      = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "either" ++ (parens $ (makeType e x) ++ ", " ++ makeType e y)
  tsum (x :: y :: z :: zs) = "either" ++ (parens $ (makeType e x) ++ ", " ++ tsum (y :: z :: zs))
makeType     e (TProd xs)     = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)       = either formatVar (?declToStr) $ Vect.index v e
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
         decl = MkDecl name (getFreeVars e)
         newEnv = Right decl :: e
         args = withSep " | " (mkArg newEnv) cs
        in
       do res <- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
          put (name :: st)
          pure $ res ++ "\ntype " ++ ?declToStr ++ " = " ++ args ++ ";\n"
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg _ (cname, T1)       = cname
  mkArg e (cname, TProd xs) = uppercase cname ++ parens (withSep ", " (makeType e) xs)
  mkArg e (cname, ctype)    = uppercase cname ++ parens (makeType e ctype)
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure "" 
       else 
        do res <- makeDefs e body 
           put (name :: st)
           pure $ res ++ "\ntype " ++ nameWithParams name e ++ " = " ++ makeType e body ++ ";\n"
  

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> String
generateType {n} = makeType (freshEnv n)

-- generate data definitions
generate : TDef n -> String
generate {n} td = evalState (makeDefs (freshEnv n) td) []

-- type definitions to be included in all outputs
helperTypes : String
helperTypes = "type void;\n\ntype either('a,'b) = Left('a) | Right('b);\n"