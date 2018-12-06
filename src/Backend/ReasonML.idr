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
  RML0 : RMLType
  RML1 : RMLType
  RMLProd : Vect (2 + k) RMLType -> RMLType
  RMLVar : Name -> RMLType
  RMLParam : Name -> RMLType -> RMLType

data ReasonML : Type where
  Synonym : Name -> Vect n Name -> RMLType -> ReasonML
  ADT     : Name -> Vect n Name -> Vect k (Name, RMLType) -> ReasonML

formatVar : String -> String
formatVar = (strCons '\'') . lowercase

nameWithParams : Name -> Env n -> String
nameWithParams name e = lowercase name ++ (withSep ", " formatVar (getFreeVars e))

typeName : Name -> List Name -> String
typeName name [] = lowercase name
typeName name ps = lowercase name ++ parens (concat $ intersperse ", " $ map formatVar ps) 

renderDef : ReasonML -> Doc
renderDef = ?renderDefImpl

renderType : RMLType -> Doc
renderType     RML0              = text "void"
renderType     RML1              = text "unit"
renderType     p@(RMLProd xs)    = tupled . toList $ map (assert_total renderType) (assert_smaller p xs)
renderType     (RMLVar v)        = text (lowercase v)
renderType     (RMLParam name params) = ?renderRMLParam

makeType : Env n -> TDef n -> RMLType
makeType = ?makeTypeImpl

makeDefs : Env n -> TDef n -> State (List Name) (List ReasonML)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (makeDefs e) xs
makeDefs e (TSum xs)     = map concat $ traverse (makeDefs e) xs
makeDefs _ (TVar v)      = pure []
makeDefs e (TMu name cs) = 
  do st <- get 
     if List.elem name st then pure [] 
      else let 
         decl = MkDecl name (getFreeVars e)
         newEnv = Right decl :: e
         args = withSep " | " (mkArg newEnv) cs
        in
       do res <- ?helpppp -- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
          put (name :: st)
          pure $ ADT name (getFreeVars e) ?argsAsVect :: res
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg _ (cname, T1)       = cname
  mkArg e (cname, TProd xs) = ?halp -- uppercase cname ++ parens (withSep ", " (makeType e) xs)
  mkArg e (cname, ctype)    = ?me -- uppercase cname ++ parens (makeType e ctype)
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- makeDefs e body 
           put (name :: st)
           pure $ Synonym name (getFreeVars e) (makeType e body) :: res

Backend ReasonML where
  generateDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode = renderDef

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv n)

-- generate data definitions
--generate : TDef n -> String
--generate {n} td = evalState (makeDefs (freshEnv n) td) []

-- type definitions to be included in all outputs
helperTypes : String
helperTypes = "type void;\n\ntype either('a,'b) = Left('a) | Right('b);\n"