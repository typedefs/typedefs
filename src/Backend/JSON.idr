module Backend.JSON

import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

import Data.Vect

%default total
%access public export

||| The syntactic structure of JSON types.
data JSONType : Type where
  ||| The `void` (i.e. empty) type. This is not a standard type
  ||| in JSON, but is useful for completeness and can be
  ||| trivially generated as needed.
  JSONVoid  :                                 JSONType

  ||| The `unit` (i.e. singleton) type.
  JSONUnit  :                                 JSONType

  ||| The tuple type, containing two or more further types.
  JSONProd  :         Vect (2 + k) JSONType -> JSONType

  ||| A type variable.
  JSONVar   :         Name                 -> JSONType

  ||| A named type with zero or more other types as parameters.
  JSONParam : Name -> Vect k JSONType       -> JSONType

||| The syntactic structure of JSON type declarations.
data JSON : Type where
  ||| A type alias is a declared name (possibly with parameters) and a type.
  Alias   : Decl -> JSONType                -> JSON

  ||| A variant is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a JSON type.
  Variant : Decl -> Vect k (Name, JSONType) -> JSON

||| Render a name as a type variable.
renderVar : Name -> Doc
renderVar v = squote |+| text (lowercase v)

||| Given a name and a vector of arguments, render an application of the name to the arguments.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text name |+| case params of
                                        [] => empty
                                        _  => tupled (toList params)

||| Render source code for a JSON type signature.
renderType : JSONType -> Doc
renderType JSONVoid                = text "void"
renderType JSONUnit                = text "unit"
renderType (JSONProd xs)           = tupled . toList $ map (assert_total renderType) xs
renderType (JSONVar v)             = renderVar v
renderType (JSONParam name params) = renderApp (lowercase name) (assert_total $ map renderType params)

-- TODO move into where-clause in 'renderDef' - why not possible?
renderConstructor : (Name, JSONType) -> Doc
renderConstructor (name, JSONUnit)       = renderApp (uppercase name) []
renderConstructor (name, JSONProd ts) = renderApp (uppercase name) (map renderType ts)
renderConstructor (name, t)          = renderApp (uppercase name) [renderType t]

||| Generate source code for a JSON type definition.
renderDef : JSON -> Doc
renderDef (Alias   decl body)  = text "type" |++| renderApp (lowercase $ name decl) (map renderVar $ params decl)
                                 |++| equals |++| renderType body
                                 |+| semi
renderDef (Variant decl cases) = text "type" |++| renderApp (lowercase $ name decl) (map renderVar $ params decl)
                                 |++| equals |++| hsep (punctuate (text " |") (toList $ map renderConstructor cases))
                                 |+| semi

||| Generate a JSON type from a TDef.
makeType : Env n -> TDef n -> JSONType
makeType     _ T0             = JSONVoid
makeType     _ T1             = JSONUnit
makeType     e (TSum xs)      = foldr1' (\t1,t2 => JSONParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType     e (TProd xs)     = JSONProd $ map (assert_total $ makeType e) xs
makeType     e (TVar v)       = either JSONVar mkParam $ Vect.index v e
  where
  mkParam : Decl -> JSONType
  mkParam (MkDecl n ps) = JSONParam n (map JSONVar ps)
makeType     e (TMu name _)   = JSONParam name (map JSONVar $ getFreeVars e)
makeType     e (TName name _) = JSONParam name (map JSONVar $ getFreeVars e)

||| Generate JSON type definitions from a TDef, includig all of its dependencies.
makeDefs : Env n -> TDef n -> State (List Name) (List JSON)
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
       do res <- map concat $ traverse {b=List JSON} (\(_, bdy) => assert_total $ makeDefs newEnv bdy) cs 
          put (name :: st)
          pure $ Variant decl cases :: res
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- assert_total $ makeDefs e body 
           put (name :: st)
           pure $ Alias (MkDecl name (getFreeVars e)) (makeType e body) :: res

Backend JSON where
  generateTyDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode        = renderDef
  freshEnv            = freshEnvLC

||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv {lang=JSON} n)