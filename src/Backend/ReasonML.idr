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
  RMLParam : Name -> Vect k RMLType -> RMLType

data ReasonML : Type where
  Synonym : Name -> Vect n Name -> RMLType -> ReasonML
  ADT     : Name -> Vect n Name -> Vect k (Name, RMLType) -> ReasonML

renderVar : String -> Doc
renderVar = text . (strCons '\'') . lowercase

withArgs : Name -> Vect n Doc -> Doc
withArgs name params = text (lowercase name) |+| case params of
                                                  [] => empty
                                                  _  => tupled (toList params)

renderType : RMLType -> Doc
renderType RML0              = text "void"
renderType RML1              = text "unit"
renderType (RMLProd xs)    = tupled . toList $ map (assert_total renderType) xs
renderType (RMLVar v)        = renderVar v
renderType (RMLParam name params) = withArgs name (assert_total $ map renderType params)
  -- text (uppercase name) |+| tupled (toList $ assert_total $ map renderType params)

-- Given a vector of parameter names, generate a single HType to be used as the parameter to HParam.
makeParamType : Vect n Name -> RMLType
makeParamType []            = RML1
makeParamType [p]           = RMLVar p
makeParamType ps@(p::q::qs) = RMLProd (map RMLVar ps)

renderConstructor : Name -> RMLType -> Doc
renderConstructor name RML1         = text name
renderConstructor name p@(RMLProd _) = (text $ uppercase name) |+| (renderType p)
renderConstructor name param     = text (uppercase name) |+| parens (renderType param)

renderDef : ReasonML -> Doc
renderDef (Synonym name vars body)  = text "type" |++| withArgs name (map renderVar vars)
                                      |++| equals |++| renderType body |+| semi
renderDef (ADT     name vars cases) = text "type" |++| withArgs name (map renderVar vars)
                                      |++| equals |++| hsep (punctuate (text " |") (toList $ map (uncurry renderConstructor) cases)) |+| semi

-- TODO this and everything related should be made much cleaner
rmlParam : Decl -> RMLType
rmlParam (MkDecl n ps) = RMLParam n (map RMLVar ps)

-- Generate a Haskell type signature from a TDef.
makeType : Env n -> TDef n -> RMLType
makeType     _ T0             = RML0
makeType     _ T1             = RML1
makeType     e (TSum xs)      = foldr1' (\t1,t2 => RMLParam "Either" ({- RMLProd -}[t1, t2])) (map (assert_total $ makeType e) xs)
makeType     e (TProd xs)     = RMLProd $ map (assert_total $ makeType e) xs
makeType     e (TVar v)       = either RMLVar rmlParam $ Vect.index v e
makeType     e (TMu name _)   = RMLParam name ({-makeParamType-} map RMLVar $ getFreeVars e)
makeType     e (TName name _) = RMLParam name ({-makeParamType-} map RMLVar $ getFreeVars e)


makeDefs : Env n -> TDef n -> State (List Name) (List ReasonML)
makeDefs _ T0            = assert_total $ makeDefs (freshEnv _) voidDef
  where
  voidDef : TDef 0
  voidDef = TMu "void" []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (assert_total $ makeDefs e) xs
makeDefs e (TSum xs)     = 
  do res <- map concat $ traverse (assert_total $ makeDefs e) xs
     map (++ res) (assert_total $ makeDefs (freshEnv _) eitherDef)
  where
  eitherDef : TDef 2
  eitherDef = TMu "either" [("Left", TVar 1), ("Right", TVar 2)]
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