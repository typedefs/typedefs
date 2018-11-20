module Backend.Haskell

import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default partial
%access public export

guardPar : String -> String
guardPar str = if any isSpace $ unpack str then parens str else str

nameWithParams : Name -> Env n -> String
nameWithParams name e = withSep " " id (uppercase name::map lowercase (getFreeVars e))

makeType : Env n -> TDef n -> Doc
makeType     _ T0             = text "Void"
makeType     _ T1             = text "()"
makeType {n} e (TSum xs)      = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> Doc
  tsum [x, y]              = text "Either" |++| parens (makeType e x) |++| parens (makeType e y)
  tsum (x :: y :: z :: zs) = text "Either" |++| parens (makeType e x) |++| parens (tsum (y :: z :: zs))
makeType     e (TProd xs)     = tupled . toList $ map (makeType e) xs
makeType     e (TVar v)       = text $ either id id $ Vect.index v e
makeType     e (TMu name _)   = text $ nameWithParams name e
makeType     e (TName name _) = text $ nameWithParams name e

makeDefs : Env n -> TDef n -> State (List Name) (List Doc)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (makeDefs e) (toList xs)
makeDefs e (TSum xs)     = map concat $ traverse (makeDefs e) (toList xs)
makeDefs _ (TVar v)      = pure []
makeDefs e (TMu name cs) = 
   do st <- get 
      if List.elem name st then pure [] 
       else let
          dataName = nameWithParams name e
          newEnv = Right (guardPar dataName) :: e
          args = sep $ punctuate (text " |") $ toList $ map (mkArg newEnv) cs
         in
        do res <- map concat $ traverse {b=List Doc} (\(_, bdy) => makeDefs newEnv bdy) (toList cs) 
           put (name :: st)
           pure $ (text "data" |++| text dataName |++| equals |++| args) :: res
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> Doc
  mkArg _ (cname, T1)       = text cname
  mkArg e (cname, TProd xs) = text cname |++| (hsep . toList) (map (makeType e) xs)
  mkArg e (cname, ctype)    = text cname |++| makeType e ctype
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- makeDefs e body 
           put (name :: st)
           pure $ (text "type" |++| text (nameWithParams name e) |++| equals |++| makeType e body) :: res

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = makeType (freshEnv n)

-- generate data definitions
generate : TDef n -> Doc
generate {n} td = vsep2 $ reverse $ evalState (makeDefs (freshEnv n) td) []