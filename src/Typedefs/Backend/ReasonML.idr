module Typedefs.Backend.ReasonML

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.Backend
import Typedefs.Backend.Utils

import Text.PrettyPrint.WL
import Control.Monad.State

import Data.NEList
import Data.Vect

%default total
%access export

||| The syntactic structure of ReasonML types.
data RMLType : Type where
  ||| The `unit` (i.e. singleton) type.
  RMLUnit  :                                  RMLType

  ||| The tuple type, containing two or more further types.
  RMLTuple  :        Vect (2 + k) RMLType -> RMLType

  ||| A type variable.
  RMLVar   :         Name                  -> RMLType

  ||| A named type with zero or more other types as parameters.
  RMLParam : Name -> Vect k RMLType        -> RMLType

||| The syntactic structure of ReasonML type declarations.
data ReasonML : Type where
  ||| A type alias is a declared name (possibly with parameters) and a type.
  Alias   : Decl -> RMLType                -> ReasonML

  ||| A variant is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a ReasonML type.
  Variant : Decl -> Vect k (Name, RMLType) -> ReasonML

-- ReasonML type variables start with an apostrophe and a lowercase letter.
private
freshEnv : Env n
freshEnv = freshEnv "'x"

||| Given a name and a vector of arguments, render an application of the name to the arguments.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = 
  text name |+| case params of
                  [] => empty
                  _  => tupled (toList params)

||| Render source code for a ReasonML type signature.
renderType : RMLType -> Doc
renderType  RMLUnit               = text "unit"
renderType (RMLTuple xs)          = tupled . toList $ map (assert_total renderType) xs
renderType (RMLVar v)             = text v
renderType (RMLParam name params) = renderApp (lowercase name) . map (assert_total renderType) $ params

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (lowercase $ name decl) (map text $ params decl)

||| Generate source code for a ReasonML type definition.
renderDef : ReasonML -> Doc
renderDef (Alias   decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
                                 |+| semi
renderDef (Variant decl cases) = 
  text "type" |++| renderDecl decl
  |+| case cases of
    [] => empty
    _  => space |+| equals 
          |++| hsep (punctuate (text " |") (toList $ map renderConstructor cases))
  |+| semi
  where
  renderConstructor : (Name, RMLType) -> Doc
  renderConstructor (name, RMLUnit)     = renderApp (uppercase name) []
  renderConstructor (name, RMLTuple ts) = renderApp (uppercase name) (map renderType ts)
  renderConstructor (name, t)           = renderApp (uppercase name) [renderType t]

private
rmlParam : Decl -> RMLType
rmlParam (MkDecl n ps) = RMLParam n (map RMLVar ps)

||| Generate a ReasonML type from a `TDef`.
makeType : Env n -> TDef n -> RMLType
makeType _     T0         = RMLParam "void" []
makeType _     T1         = RMLUnit
makeType e    (TSum xs)   = foldr1' (\t1,t2 => RMLParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType e    (TProd xs)  = RMLTuple . map (assert_total $ makeType e) $ xs
makeType e    (TVar v)    = either RMLVar rmlParam $ Vect.index v e
makeType e td@(TMu cases) = RMLParam (nameMu cases) . map (either RMLVar rmlParam) $ getUsedVars e td
makeType e    (TApp f xs) = RMLParam (name f) (map (assert_total $ makeType e) xs)

||| Generate a ReasonML type from a `TNamed`.
makeType' : Env n -> TNamed n -> RMLType
makeType' e (TName name body) = RMLParam name . map (either RMLVar rmlParam) $ getUsedVars e body

mutual
  ||| Generate all the ReasonML type definitions that a `TDef` depends on.
  makeDefs : TDef n -> State (List Name) (List ReasonML)
  makeDefs T0             = assert_total $ makeDefs' voidDef
    where
    voidDef : TNamed 0
    voidDef = TName "void" $ TMu []
  makeDefs T1             = pure []
  makeDefs (TProd xs)     = map concat $ traverse (assert_total makeDefs) xs
  makeDefs (TSum xs)      = 
    do res <- map concat $ traverse (assert_total makeDefs) xs
       map (++ res) (assert_total $ makeDefs' eitherDef)
    where
    eitherDef : TNamed 2
    eitherDef = TName "either" $ TMu [("Left", TVar 1), ("Right", TVar 2)]
  makeDefs    (TVar v)    = pure []
  makeDefs td@(TMu cases) = makeDefs' $ TName (nameMu cases) td -- We name anonymous mus using their constructors.
  makeDefs    (TApp f xs) = 
    do res <- assert_total $ makeDefs' f
       res' <- concat <$> traverse (assert_total makeDefs) xs
       pure (res ++ res')

  ||| Generate ReasonML type definitions for a `TNamed` and all of its dependencies.
  makeDefs' : TNamed n -> State (List Name) (List ReasonML)
  makeDefs' (TName name body) = ifNotPresent name $
      let decl = MkDecl name (getFreeVars $ getUsedVars freshEnv body) in -- All vars will actually be free, but we want Strings instead of Eithers.
      case body of
        TMu cases =>
          -- Named `TMu`s are treated as ADTs. 
          do let newEnv = Right decl :: freshEnv
             let args = map (map (makeType newEnv)) cases
             res <- map concat $ traverse {b=List ReasonML} (\(_, bdy) => assert_total $ makeDefs bdy) (toList cases)
             pure $ res ++ [Variant decl args]
        _ => 
          -- All other named types are treated as synonyms.
          do res <- assert_total $ makeDefs body
             pure $ res ++ [Alias decl (makeType freshEnv body)]

ASTGen ReasonML RMLType True where
  msgType  (Unbounded tn) = makeType' freshEnv tn
  generateTyDefs tns = 
    evalState 
      (foldlM (\lh,(Unbounded tn) => (lh ++) <$> (makeDefs' tn)) [] tns) 
      (the (List Name) [])
  generateTermDefs tns = [] -- TODO

CodegenIndep ReasonML RMLType where
  typeSource = renderType
  defSource  = renderDef
  preamble   = empty -- TODO
