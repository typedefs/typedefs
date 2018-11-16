module Backend.Utils

import Data.Vect

%default total
%access public export

Env : Nat -> Type
Env k = Vect k (Either String String) -- left=free / right=bound

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

freshEnv : (n: Nat) -> Env n
freshEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

withSep : String -> (a -> String) -> Vect k a -> String
withSep sep fn xs = concat $ intersperse sep $ map fn xs

getFreeVars : (e : Env n) -> (String -> String) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e f with (filter isLeft e) 
  getFreeVars e f | (p ** v) = map (either f (const "")) v