module Backend.Haskell

import Data.Vect
import Prelude.Nat

import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Backend

import Types
import Typedefs

%default total
%access public export

||| The syntactic structure of Haskell types.
data HsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  HsVoid  :                                HsType

  ||| The `()` (i.e. unit/singleton) type.
  HsUnit  :                                HsType

  ||| The tuple type, containing two or more further types.
  HsTuple :         Vect (2 + k) HsType -> HsType

  ||| A type variable.
  HsVar   :         Name                -> HsType

  ||| A named type with zero or more other types as parameters.
  HsParam : Name -> Vect k HsType       -> HsType

||| The syntactic structure of Haskell type declarations.
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect k (Name, HsType) -> Haskell

||| Render a name applied to a list of arguments exactly as written.
||| Arguments need to be previously parenthesized, if applicable.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  ||| Render a type signature as Haskell source code. 
  renderType : HsType -> Doc
  renderType HsVoid                = text "Void"
  renderType HsUnit                = text "()"
  renderType (HsTuple xs)          = tupled . toList $ map (assert_total renderType) xs
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)
  
  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : HsType -> Doc
  guardParen t@(HsParam _ []) = assert_total $ renderType t
  guardParen t@(HsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

||| Render a type definition as Haskell source code.
renderDef : Haskell -> Doc
renderDef (Synonym decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
renderDef (ADT     decl cases) = text "data" |++| renderDecl decl
                                 |++| equals |++| hsep (punctuate (text " |")
                                                       (toList $ map renderConstructor cases))
  where
  renderConstructor : (Name, HsType) -> Doc
  renderConstructor (name, HsUnit)     = renderApp name []
  renderConstructor (name, HsTuple ts) = renderApp name (map guardParen ts)
  renderConstructor (name, params)     = renderApp name [guardParen params]

||| Generate a Haskell type from a TDef.
makeType : Env n -> TDef n -> HsType
makeType _ T0             = HsVoid
makeType _ T1             = HsUnit
makeType e (TSum xs)      = foldr1' (\t1,t2 => HsParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType e (TProd xs)     = HsTuple $ map (assert_total $ makeType e) xs
makeType e (TVar v)       = either HsVar hsParam $ Vect.index v e
  where
  hsParam : Decl -> HsType
  hsParam (MkDecl n ps) = HsParam n (map HsVar ps)
makeType e td@(TMu name _)   = HsParam name $ map HsVar (getFreeVars (getUsedVars e td))
makeType e td@(TName name _) = HsParam name $ map HsVar (getFreeVars (getUsedVars e td))

||| Generate Haskell type definitions from a TDef, including all of its dependencies.
makeDefs : Env n -> TDef n -> State (List Name) (List Haskell)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (assert_total $ makeDefs e) (toList xs)
makeDefs e (TSum xs)     = map concat $ traverse (assert_total $ makeDefs e) (toList xs)
makeDefs _ (TVar v)      = pure []
makeDefs e td@(TMu name cs) = 
   do st <- get 
      if List.elem name st then pure [] 
       else let
          decl = MkDecl name (getFreeVars (getUsedVars e td))
          newEnv = Right decl :: e
          args = map (map (makeType newEnv)) cs
         in
        do res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs newEnv bdy) (toList cs) 
           put (name :: st)
           pure $ ADT decl args :: res
makeDefs e td@(TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- assert_total $ makeDefs e body 
           put (name :: st)
           pure $ Synonym (MkDecl name $ getFreeVars (getUsedVars e td)) (makeType e body) :: res

Backend Haskell where
  generateTyDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode        = renderDef
  freshEnv            = freshEnvLC

||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv {lang=Haskell} n)
