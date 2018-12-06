module Backend.ReasonML

import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default total
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

bajs : Name -> Vect n Name -> Doc
bajs name params = text name |+| tupled (toList $ map text params)

renderType : RMLType -> Doc
renderType RML0              = text "void"
renderType RML1              = text "unit"
renderType (RMLProd xs)    = tupled . toList $ map (assert_total renderType) xs
renderType (RMLVar v)        = text (lowercase v)
renderType (RMLParam name params) = ?renderRMLParam

-- Given a vector of parameter names, generate a single HType to be used as the parameter to HParam.
makeParamType : Vect n Name -> RMLType
makeParamType []            = RML1
makeParamType [p]           = RMLVar p
makeParamType ps@(p::q::qs) = RMLProd (map RMLVar ps)


renderDef : ReasonML -> Doc
renderDef (Synonym name vars body)  = text "type" |++| bajs name vars
                                      |++| equals |++| renderType body
renderDef (ADT     name vars cases) = text "type" |++| bajs name vars
                                      |++| equals |++| hsep (punctuate (text " |") (toList $ map ?lerl cases))

-- Generate a Haskell type signature from a TDef.
makeType : Env n -> TDef n -> RMLType
makeType     _ T0             = RML0
makeType     _ T1             = RML1
makeType     e (TSum xs)      = foldr1' (\t1,t2 => RMLParam "Either" (RMLProd [t1, t2])) (map (assert_total $ makeType e) xs)
makeType     e (TProd xs)     = RMLProd $ map (assert_total $ makeType e) xs
makeType     e (TVar v)       = either RMLVar ?hParam $ Vect.index v e
makeType     e (TMu name _)   = RMLParam name (makeParamType $ getFreeVars e)
makeType     e (TName name _) = RMLParam name (makeParamType $ getFreeVars e)

makeDefs : Env n -> TDef n -> State (List Name) (List ReasonML)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (assert_total $ makeDefs e) xs
makeDefs e (TSum xs)     = map concat $ traverse (assert_total $ makeDefs e) xs
makeDefs _ (TVar v)      = pure []
makeDefs e (TMu name cs) = 
  do st <- get 
     if List.elem name st then pure [] 
      else let 
         decl = MkDecl name (getFreeVars e)
         newEnv = Right decl :: e
         cases = map (map (makeType newEnv)) cs
        in
       do res <- map concat $ traverse {b=List ReasonML} (\(_, bdy) => assert_total $ makeDefs newEnv bdy) cs 
          put (name :: st)
          pure $ ADT name (getFreeVars e) cases :: res
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- assert_total $ makeDefs e body 
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