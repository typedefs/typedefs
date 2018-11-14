module Backend.Haskell

import Data.Vect
--import Decidable.Equality
import Control.Monad.State

import Types
import Typedefs

%default partial
%access public export

Env : Nat -> Type
Env k = Vect k (Either String String) -- left=free / right=bound

withSep : String -> (a -> String) -> Vect k a -> String
withSep sep fn xs = concat $ intersperse sep $ map fn xs

guardPar : String -> String
guardPar str = if any isSpace $ unpack str then parens str else str

-- TODO would be nice if type was `(e : Env n) -> Vect (fst (Vect.filter isLeft e)) String`, 
-- since it then could be used by several backends. I'm having trouble getting it to typecheck.
getFreeVars : Env n -> String
getFreeVars e = withSep " " (either id (const "")) $ snd $ Vect.filter isLeft e

makeType : Env n -> TDef n -> String
makeType     _ T0            = "Void"
makeType     _ T1            = "()"
makeType {n} e (TSum xs)     = tsum xs
  where
  tsum : Vect (2 + _) (TDef n) -> String
  tsum [x, y]              = "Either " ++ guardPar (makeType e x) ++ " " ++ guardPar (makeType e y)
  tsum (x :: y :: z :: zs) = "Either " ++ guardPar (makeType e x) ++ " " ++ parens (tsum (y :: z :: zs))
makeType     e (TProd xs)    = assert_total $ parens $ withSep ", " (makeType e) xs
makeType     e (TVar v)      = either id id $ Vect.index v e
makeType     e (TMu nam _)   = let freeVars = getFreeVars e
                                in if freeVars == "" then nam else nam ++ " " ++ freeVars
makeType     _ (TName nam _) = nam

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
         freeVars = getFreeVars e
         dataName = if freeVars == "" then nam else nam ++ " " ++ freeVars
         newEnv = Right (if freeVars == "" then dataName else parens dataName) :: e
         args = withSep " | " (mkArg newEnv) cs
        in
       do res <- map concat $ traverse {b=String} (\(_, bdy) => makeDefs newEnv bdy) cs 
          put (nam :: st)
          pure $ res ++ "\ndata " ++ dataName ++ " = " ++ args ++ "\n"
  where
  mkArg : Env (S n) -> (Name, TDef (S n)) -> String
  mkArg _ (cname, T1)       = cname
  mkArg e (cname, TProd xs) = cname ++ " " ++ withSep " " (makeType e) xs
  mkArg e (cname, ctype)    = cname ++ " " ++ makeType e ctype
makeDefs e (TName nam body) = 
  do st <- get 
     if List.elem nam st then pure "" 
       else let 
          freeVars = getFreeVars e
          typeName = if freeVars == "" then nam else nam ++ " " ++ freeVars
         in
        do res <- makeDefs e body 
           put (nam :: st)
           pure $ res ++ "\ntype " ++ typeName ++ " = " ++ makeType e body ++ "\n"

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

