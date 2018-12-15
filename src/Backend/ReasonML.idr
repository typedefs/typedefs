module Backend.ReasonML

import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

import Data.Vect

%default total
%access public export

||| The syntactic structure of ReasonML types.
data RMLType : Type where
  ||| The `void` (i.e. empty) type. This is not a standard type
  ||| in ReasonML, but is useful for completeness and can be
  ||| trivially generated as needed.
  RMLVoid  :                                 RMLType

  ||| The `unit` (i.e. singleton) type.
  RMLUnit  :                                 RMLType

  ||| The tuple type, containing two or more further types.
  RMLProd  :         Vect (2 + k) RMLType -> RMLType

  ||| A type variable.
  RMLVar   :         Name                 -> RMLType

  ||| A named type with zero or more other types as parameters.
  RMLParam : Name -> Vect k RMLType       -> RMLType

||| The syntactic structure of ReasonML type declarations.
data ReasonML : Type where
  ||| A type alias is a declared name (possibly with parameters) and a type.
  Alias   : Decl -> RMLType                -> ReasonML

  ||| A variant is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a ReasonML type.
  Variant : Decl -> Vect k (Name, RMLType) -> ReasonML

||| Render a name as a type variable.
renderVar : Name -> Doc
renderVar v = squote |+| text (lowercase v)

||| Given a name and a vector of arguments, render an application of the name to the arguments.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text name |+| case params of
                                        [] => empty
                                        _  => tupled (toList params)

||| Render source code for a ReasonML type signature.
renderType : RMLType -> Doc
renderType RMLVoid                = text "void"
renderType RMLUnit                = text "unit"
renderType (RMLProd xs)           = tupled . toList $ map (assert_total renderType) xs
renderType (RMLVar v)             = renderVar v
renderType (RMLParam name params) = renderApp (lowercase name) (assert_total $ map renderType params)

-- TODO move into where-clause in 'renderDef' - why not possible?
renderConstructor : (Name, RMLType) -> Doc
renderConstructor (name, RMLUnit)       = renderApp (uppercase name) []
renderConstructor (name, RMLProd ts) = renderApp (uppercase name) (map renderType ts)
renderConstructor (name, t)          = renderApp (uppercase name) [renderType t]

||| Generate source code for a ReasonML type definition.
renderDef : ReasonML -> Doc
renderDef (Alias   decl body)  = text "type" |++| renderApp (lowercase $ name decl) (map renderVar $ params decl)
                                 |++| equals |++| renderType body
                                 |+| semi
renderDef (Variant decl cases) = text "type" |++| renderApp (lowercase $ name decl) (map renderVar $ params decl)
                                 |++| equals |++| hsep (punctuate (text " |") (toList $ map renderConstructor cases))
                                 |+| semi

||| Generate a ReasonML type from a TDef.
makeType : Env n -> TDef n -> RMLType
makeType     _ T0             = RMLVoid
makeType     _ T1             = RMLUnit
makeType     e (TSum xs)      = foldr1' (\t1,t2 => RMLParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType     e (TProd xs)     = RMLProd $ map (assert_total $ makeType e) xs
makeType     e (TVar v)       = either RMLVar mkParam $ Vect.index v e
  where
  mkParam : Decl -> RMLType
  mkParam (MkDecl n ps) = RMLParam n (map RMLVar ps)
makeType     e (TMu name _)   = RMLParam name (map RMLVar $ getFreeVars e)
makeType     e (TName name _) = RMLParam name (map RMLVar $ getFreeVars e)

||| Generate ReasonML type definitions from a TDef, includig all of its dependencies.
makeDefs : Env n -> TDef n -> State (List Name) (List ReasonML)
makeDefs _ T0            = assert_total $ makeDefs (freshEnvLC _) voidDef
  where
  voidDef : TDef 0
  voidDef = TMu "void" []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (assert_total $ makeDefs e) xs
makeDefs e (TSum xs)     = 
  do res <- map concat $ traverse (assert_total $ makeDefs e) xs
     map (++ res) (assert_total $ makeDefs (freshEnvLC _) eitherDef)
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
          pure $ Variant decl cases :: res
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- assert_total $ makeDefs e body 
           put (name :: st)
           pure $ Alias (MkDecl name (getFreeVars e)) (makeType e body) :: res

Backend ReasonML where
  generateTyDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode        = renderDef
  freshEnv            = freshEnvLC

||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv {lang=ReasonML} n)