module TermCodec

import Data.Vect
import Data.Vect.Quantifiers

import Typedefs
import Types

%default total
%access public export

mutual 

  serializeMu : {ts : Vect n (t: Type ** t -> String)} -> Mu (map DPair.fst ts) td -> String
  serializeMu {ts} {td} (Inn x) = assert_total $ serialize {ts=(Mu (map DPair.fst ts) td ** serializeMu)::ts} td x

  serialize : {ts : Vect n (t: Type ** t -> String)} -> (t : TDef n) -> (tm : Ty (map DPair.fst ts) t) -> String
  serialize                                T1                                   ()        =
    "()"
  
  serialize                                (TSum [x,y])                         (Left l)  = 
    "(left " ++ serialize x l ++ ")"
  
  serialize                                (TSum [x,y])                         (Right r) = 
    "(right " ++ serialize y r ++ ")"
  
  serialize                                (TSum (x::y::z::zs))                 (Left l)  = 
    "(left " ++ serialize x l ++ ")"
  
  serialize                                (TSum (x::y::z::zs))                 (Right r) =
    "(right " ++ serialize  (TSum (y::z::zs)) r ++ ")"
  
  serialize                                (TProd [x,y])                        (a, b)    = 
    "(both " ++ serialize x a ++ " " ++ serialize y b ++ ")"
  
  serialize                                (TProd (x::y::z::zs))                (a, b)    = 
    "(both " ++ serialize x a ++ " " ++ serialize (TProd (y::z::zs)) b ++ ")"
  serialize {ts=(t**f)::ts} (TVar FZ)   x = f x
  serialize {ts=_::(t**f) :: ts} (TVar (FS FZ))   x = f x --serialize {ts} (TVar i) ?wat
  serialize {ts=_::ts} (TVar (FS (FS i)))   x = serialize {ts} (TVar (FS i)) x
  --  let foo = index i (ts) in 
    
  serialize {ts}       (TMu nm td)    (Inn x) = 
      with Strings (
          "(inn " ++ 
            serialize {ts=((Mu (map DPair.fst ts) (args td)) ** serializeMu)::ts} (args td) x ++ 
            ")"
          )

  serialize (TName nam td) x = serialize td x
