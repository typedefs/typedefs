module Backend.Haskell

import Data.Vect
import Control.Monad.State

import Types
import Typedefs

%default partial
%access public export

Env : Nat -> Type
Env k = Vect k (Either String String) -- left free / right bound

withSep : String -> (a -> String) -> Vect k a -> String
withSep sep fn xs = concat $ intersperse sep $ map fn xs

withSep' : String -> (a -> String) -> List a -> String
withSep' sep fn xs = concat $ intersperse sep $ map fn xs

guardPar : String -> String
guardPar str = if any isSpace $ unpack str then parens str else str

makeType : Env n -> TDef n -> String
makeType     _ T0            = "Void"
makeType     _ T1            = "Unit"
makeType {n} e (TSum xs)     = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "Either " ++ guardPar (makeType e x) ++ " " ++ guardPar (makeType e y)
  tsum (x :: y :: z :: zs) = "Either " ++ guardPar (makeType e x) ++ " " ++ parens (tsum (y :: z :: zs))
makeType     e (TProd xs)    = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)      = either id id $ Vect.index v e
makeType     _ (TMu nam _)   = nam
makeType     _ (TName nam _) = nam

makeDefs : Env n -> TDef n -> State (List Name) String
makeDefs     _ T0           = pure ""
makeDefs     _ T1           = pure ""
makeDefs     e (TProd xs)   = map concat $ traverse (makeDefs e) xs
makeDefs     e (TSum xs)    = map concat $ traverse (makeDefs e) xs
makeDefs     _ (TVar v)     = pure ""
makeDefs {n} e (TMu nam cs) = 
  do st <- get 
     if List.elem nam st then pure "" 
      else let
             freeVars = withSep " " (either id (const "")) $ snd $ Vect.filter isLeft e
             dataName = if freeVars == "" then nam else nam ++ " " ++ freeVars
             newEnv = (Right (if freeVars == "" then dataName else parens dataName) :: e)
             args = withSep' " | " (mkArg newEnv) cs
           in
             do res <- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
                put (nam :: st)
                pure $ res ++ "\ndata " ++ dataName ++ " = " ++ args ++ "\n"
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg e (cname,  T1)        = cname
  mkArg e (cname, (TProd xs)) = cname ++ " " ++ (withSep " " (makeType e) xs)
  mkArg e (cname, ctype)      = cname ++ " " ++ makeType e ctype
  
makeDefs    e (TName nam body) = 
  do st <- get 
     if List.elem nam st then pure "" 
       else do res <- makeDefs e body 
               put (nam :: st)
               let freeVars = withSep " " (either id (const "")) $ snd $ Vect.filter isLeft e
               let typeName = if freeVars == "" then nam else nam ++ " " ++ freeVars
               pure $ res ++ "\ntype " ++ typeName ++ " = " ++ makeType e body ++ "\n"

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n = Z} _ = []
unindex {n = S k} f = f FZ :: unindex (f . FS)  

freshEnv : (n: Nat) -> Env n
freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

generate : TDef n -> String
generate {n} td = evalState (makeDefs (freshEnv n) td) []      

generateType : TDef n -> String
generateType {n} = makeType (freshEnv n)