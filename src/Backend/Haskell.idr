module Backend.Haskell

import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default total
%access public export

data HType : Type where
  H0     :                               HType
  H1     :                               HType
  HProd  :         Vect (2 + k) HType -> HType
  HVar   :         Name               -> HType
  HParam : Name -> Vect k HType       -> HType

data Haskell : Type where
  Synonym : Decl -> HType                -> Haskell
  ADT     : Decl -> Vect k (Name, HType) -> Haskell

-- Render a name applied to a list of arguments exactly as written (arguments need to be previously parenthesized, if applicable).
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  -- Render a type signature as Haskell source code. 
  renderType : HType -> Doc
  renderType H0                   = text "Void"
  renderType H1                   = text "()"
  renderType p@(HProd xs)         = tupled . toList $ map (assert_total renderType) xs
  renderType (HVar v)             = text (lowercase v)
  renderType (HParam name params) = renderApp name (map guardParen params)
  
  -- As 'renderType', but with enclosing parentheses if it can possibly make a semantic difference.
  guardParen : HType -> Doc
  guardParen t@(HParam _ []) = assert_total $ renderType t
  guardParen t@(HParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t               = assert_total $ renderType t

-- Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

-- Render a type definition as Haskell source code.
renderDef : Haskell -> Doc
renderDef (Synonym decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
renderDef (ADT     decl cases) = text "data" |++| renderDecl decl
                                 |++| equals |++| hsep (punctuate (text " |")
                                                       (toList $ map (uncurry renderConstructor) cases))
  where
  renderConstructor : Name -> HType -> Doc
  renderConstructor name H1         = renderApp name []
  renderConstructor name (HProd ts) = renderApp name (map guardParen ts)
  renderConstructor name params     = renderApp name [guardParen params]

-- Generate a Haskell type from a TDef.
makeType : Env n -> TDef n -> HType
makeType     _ T0             = H0
makeType     _ T1             = H1
makeType     e (TSum xs)      = foldr1' (\t1,t2 => HParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType     e (TProd xs)     = HProd $ map (assert_total $ makeType e) xs
makeType     e (TVar v)       = either HVar hParam $ Vect.index v e
  where
  hParam : Decl -> HType
  hParam (MkDecl n ps) = HParam n (map HVar ps)
makeType     e (TMu name _)   = HParam name (map HVar $ getFreeVars e)
makeType     e (TName name _) = HParam name (map HVar $ getFreeVars e)

-- Generate Haskell type definitions from a TDef, including all of its dependencies.
makeDefs : Env n -> TDef n -> State (List Name) (List Haskell)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (assert_total $ makeDefs e) (toList xs)
makeDefs e (TSum xs)     = map concat $ traverse (assert_total $ makeDefs e) (toList xs)
makeDefs _ (TVar v)      = pure []
makeDefs e (TMu name cs) = 
   do st <- get 
      if List.elem name st then pure [] 
       else let
          decl = MkDecl name (getFreeVars e)
          newEnv = Right decl :: e
          args = map (map (makeType newEnv)) cs
         in
        do res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs newEnv bdy) (toList cs) 
           put (name :: st)
           pure $ ADT decl args :: res
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- assert_total $ makeDefs e body 
           put (name :: st)
           pure $ Synonym (MkDecl name (getFreeVars e)) (makeType e body) :: res

Backend Haskell where
  generateDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode      = renderDef

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv n)