module Backend.Haskell

import Data.HVect
import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default total
%access public export

{-
TODO
 Remove TDef -> String funs
 Rename funs
 clean up totality assertions
 index Haskell type by vars?
 use Decl in Haskell/RML
 consistent naming (vars/params, constructors/cases, ...) 
 consistent application of toList (after/before map)
 take care of upper/lowercase when prettyprinting
 use Either Type ConstructorList instead of ADT/Syn?
 use Vect n RMLType instead of RMLType in RMLParam
-}

data HType : Type where
  H0     :                               HType
  H1     :                               HType
  HProd  :         Vect (2 + k) HType -> HType
  HVar   :         Name               -> HType
  HParam : Name -> Vect k HType       -> HType

data Haskell : Type where
  Synonym : (name : Name) -> (vars : Vect n Name) -> HType                -> Haskell
  ADT     : (name : Name) -> (vars : Vect n Name) -> Vect k (Name, HType) -> Haskell

renderDecl : Name -> Vect n Name -> Doc
renderDecl name params = text (uppercase name) |+| hsep (toList $ empty :: map text params)

mutual
  -- Generate Haskell code for a Haskell type signature.
  renderType : HType -> Doc
  renderType H0              = text "Void"
  renderType H1              = text "()"
  renderType p@(HProd xs)    = tupled . toList $ map (assert_total renderType) xs
  renderType (HVar v)        = text (lowercase v)
  renderType (HParam name params) = withArgs name params

  -- Generate parenthesized type signature, if needed.
  guardParen : HType -> Doc
  guardParen ht = assert_total $ if isSimple ht then renderType ht else parens (renderType ht)
    where
    isSimple : HType -> Bool
    isSimple (HParam _ t) = case t of
                              [] => True
                              _  => False
    isSimple _            = True
  
  -- TODO rewrite doc for this?; where is it actually used?
  -- Generate a name followed by arguments. Is used both for constructors and for parametric types.
  withArgs : Name -> Vect n HType -> Doc
  withArgs name params = text (uppercase name) |+| hsep (toList $ empty :: map guardParen params)

renderConstructor : Name -> HType -> Doc
renderConstructor name H1         = withArgs name []
renderConstructor name (HProd ts) = withArgs name ts
renderConstructor name params     = withArgs name [params]

-- Generate Haskell code for a Haskell type definition.
renderDef : Haskell -> Doc
renderDef (Synonym name vars body)  = text "type" |++| renderDecl name vars
                                      |++| equals |++| renderType body
renderDef (ADT     name vars cases) = text "data" |++| renderDecl name vars
                                      |++| equals |++| hsep (punctuate (text " |") (toList $ map (uncurry renderConstructor) cases))

-- TODO this and everything related should be made much cleaner
hParam : Decl -> HType
hParam (MkDecl n ps) = HParam n (map HVar ps)

-- Generate a Haskell type signature from a TDef.
makeType : Env n -> TDef n -> HType
makeType     _ T0             = H0
makeType     _ T1             = H1
makeType     e (TSum xs)      = foldr1' (\t1,t2 => HParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType     e (TProd xs)     = HProd $ map (assert_total $ makeType e) xs
makeType     e (TVar v)       = either HVar hParam $ Vect.index v e
makeType     e (TMu name _)   = HParam name (map HVar $ getFreeVars e)
makeType     e (TName name _) = HParam name (map HVar $ getFreeVars e)

-- Generate a list of Haskell type definitions from a TDef. 
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
          newEnv = Right (MkDecl name $ getFreeVars e) :: e
          args = map (map (makeType newEnv)) cs
         in
        do res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs newEnv bdy) (toList cs) 
           put (name :: st)
           pure $ ADT name (getFreeVars e) args :: res
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- assert_total $ makeDefs e body 
           put (name :: st)
           pure $ Synonym name (getFreeVars e) (makeType e body) :: res

Backend Haskell where
  --generate {n} td = vsep2 . map renderDef . reverse $ evalState (makeDefs (freshEnv n) td) []
  generateDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode = renderDef

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv n)

-- generate data definitions
--generate : TDef n -> Src Haskell
--generate {n} td = vsep2 . map renderDef . reverse $ evalState (makeDefs (freshEnv n) td) []