module Backend.Haskell

import Data.HVect
import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default partial
%access public export

{-
TODO
 Remove TDef -> String funs
 Rename funs
 Move and rename SynEnv
-}

data HType : Type where
  H0     :                               HType
  H1     :                               HType
  HProd  :         Vect (2 + k) HType -> HType
  HVar   :         Name               -> HType
  HParam : Name -> HType              -> HType

data HDef : Type where
  Synonym : (name : Name) -> (vars : Vect n Name) -> HType                -> HDef
  ADT     : (name : Name) -> (vars : Vect n Name) -> Vect k (Name, HType) -> HDef

mutual
  -- Generate Haskell code for a Haskell type signature.
  renderType : HType -> Doc
  renderType H0              = text "Void"
  renderType H1              = text "()"
  renderType (HProd xs)      = tupled . toList $ map renderType xs
  renderType (HVar v)        = text (lowercase v)
  renderType (HParam name t) = withArgs name t

  -- Generate parenthesized type signature, if needed.
  guardParen : HType -> Doc
  guardParen ht = if isSimple ht then renderType ht else parens (renderType ht)
    where
    isSimple : HType -> Bool
    isSimple (HParam _ t) = case t of
                              H1 => True
                              _  => False
    isSimple _            = True
  
  -- Generate a name followed by arguments. Is used both for constructors and for parametric types.
  withArgs : Name -> HType -> Doc
  withArgs n H1         = text (uppercase n)
  withArgs n (HProd ts) = text (uppercase n) |++| hsep (toList (map guardParen ts))
  withArgs n ht         = text (uppercase n) |++| renderType ht

-- Given a vector of parameter names, generate a single HType to be used as the parameter to HParam.
makeParamType : Vect n Name -> HType
makeParamType []            = H1
makeParamType [p]           = HVar p
makeParamType ps@(p::q::qs) = HProd (map HVar ps)

-- Generate Haskell code for a Haskell type definition.
renderDef : HDef -> Doc
renderDef (Synonym name vars body)  = text "type" |++| withArgs name (makeParamType vars)
                                   |++| equals |++| renderType body
renderDef (ADT     name vars cases) = text "data" |++| withArgs name (makeParamType vars)
                                   |++| equals |++| hsep (punctuate (text " |") (toList $ map (uncurry withArgs) cases))

SynEnv : Nat -> Type
SynEnv n = Vect n (Either Name (Name, HType))

-- Creates an environment with n free variables.
freshSynEnv : (n: Nat) -> SynEnv n
freshSynEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

-- Extracts the free variables from the environment.
getFreeVars : (e : SynEnv n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e) 
  | (p ** v) = map (either id (const "")) v

-- Custom foldr1 because the standard one doesn't handle base case correctly.
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

-- Generate a Haskell type signature from a TDef.
makeType : SynEnv n -> TDef n -> HType
makeType     _ T0             = H0
makeType     _ T1             = H1
makeType     e (TSum xs)      = foldr1' (\t1,t2 => HParam "Either" (HProd [t1, t2])) (map (makeType e) xs)
makeType     e (TProd xs)     = HProd $ map (makeType e) xs
makeType     e (TVar v)       = either HVar (uncurry HParam) $ Vect.index v e
makeType     e (TMu name _)   = HParam name (makeParamType $ getFreeVars e)
makeType     e (TName name _) = HParam name (makeParamType $ getFreeVars e)

-- Generate a list of Haskell type definitions from a TDef. 
makeDefs : SynEnv n -> TDef n -> State (List Name) (List HDef)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (makeDefs e) (toList xs)
makeDefs e (TSum xs)     = map concat $ traverse (makeDefs e) (toList xs)
makeDefs _ (TVar v)      = pure []
makeDefs e (TMu name cs) = 
   do st <- get 
      if List.elem name st then pure [] 
       else let
          newEnv = Right (name, makeParamType $ getFreeVars e) :: e
          args = map (map (makeType newEnv)) cs
         in
        do res <- map concat $ traverse {b=List HDef} (\(_, bdy) => makeDefs newEnv bdy) (toList cs) 
           put (name :: st)
           pure $ ADT name (getFreeVars e) args :: res
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- makeDefs e body 
           put (name :: st)
           pure $ Synonym name (getFreeVars e) (makeType e body) :: res

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshSynEnv n)

-- generate data definitions
generate : TDef n -> Doc
generate {n} td = vsep2 . map renderDef . reverse $ evalState (makeDefs (freshSynEnv n) td) []