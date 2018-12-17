module Backend.Utils

import Typedefs
import Types
import Backend

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export


-- TODO implementation in base was erroneous, this has been merged but is not in a version yet. 
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

||| Print a document with a width of 80 symbols.
print : Doc -> String
print = toString 1 80

||| Standard implmementation of `freshEnv` for languages that require type parameters to
||| start with lower case letters (and allow numbers in names).
freshEnvLC : (n : Nat) -> Env n
freshEnvLC n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

||| Standard implmementation of `freshEnv` for languages that require type parameters to
||| start with upper case letters (and allow numbers in names).
freshEnvUC : (n : Nat) -> Env n
freshEnvUC n = unindex {n} (\f => Left ("X" ++ show (finToInteger f)))