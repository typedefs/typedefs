module Backend.ReasonML

import Data.Vect
import Control.Monad.State

import Types
import Typedefs

%default partial
%access public export

Env : Nat -> Type
Env k = Vect k (Either String String) -- left=free / right=bound

withSep : String -> (a -> String) -> Vect k a -> String
withSep sep fn xs = concat $ intersperse sep $ map fn xs


formatVar : String -> String
formatVar = ("'" ++) . lowercase


makeType : Env n -> TDef n -> String
makeType     _ T0            = ?emptyType
makeType     _ T1            = "unit"
makeType {n} e (TSum xs)     = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "either" ++ (parens $ (makeType e x) ++ ", " ++ makeType e y)
  tsum (x :: y :: z :: zs) = "either" ++ (parens $ (makeType e x) ++ ", " ++ tsum (y :: z :: zs))
makeType     e (TProd xs)    = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)      = either formatVar lowercase $ Vect.index v e
makeType     _ (TMu nam _)   = lowercase nam
makeType     _ (TName nam _) = lowercase nam

makeDefs : Env n -> TDef n -> State (List Name) String
makeDefs _ T0           = pure ""
makeDefs _ T1           = pure ""
makeDefs e (TProd xs)   = map concat $ traverse (makeDefs e) xs
makeDefs e (TSum xs)    = map concat $ traverse (makeDefs e) xs
makeDefs _ (TVar v)     = pure ""
makeDefs e (TMu nam cs) = 
  do st <- get 
     if List.elem nam st then pure "" 
      else let
         freeVars = withSep ", " (either formatVar (const "")) $ snd $ Vect.filter isLeft e
         dataName = if freeVars == "" then nam else nam ++ parens freeVars
         newEnv = Right (if freeVars == "" then dataName else dataName) :: e
         args = withSep " | " (mkArg newEnv) cs
        in
       do res <- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
          put (nam :: st)
          pure $ res ++ "\ntype " ++ lowercase dataName ++ " = " ++ args ++ ";\n"
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg _ (cname, T1)       = cname
  mkArg e (cname, TProd xs) = uppercase cname ++ parens (withSep ", " (makeType e) xs)
  mkArg e (cname, ctype)    = uppercase cname ++ parens (makeType e ctype)
makeDefs e (TName nam body) = 
  do st <- get 
     if List.elem nam st then pure "" 
       else let 
          freeVars = withSep ", " (either formatVar (const "")) $ snd $ Vect.filter isLeft e
          typeName = if freeVars == "" then nam else nam ++ parens freeVars
         in
        do res <- makeDefs e body 
           put (nam :: st)
           pure $ res ++ "\ntype " ++ typeName ++ " = " ++ makeType e body ++ ";\n"

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)  

freshEnv : (n: Nat) -> Env n
freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> String
generateType {n} = makeType (freshEnv n)

-- generate data definitions
generate : TDef n -> String
generate {n} td = evalState (makeDefs (freshEnv n) td) []      

-- type definitions to be included in all outputs
helperTypes : String
helperTypes = "type either('a,'b) = Left('a) | Right('b)"


