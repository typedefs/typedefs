module TermWrite

import Typedefs
import Types

import Data.Vect

%default total
%access public export

-- serialization

data HasWriters : Vect n Type -> Type where
  Nil : HasWriters Nil
  (::) : {xs : Vect n Type} -> (x -> String) -> HasWriters xs -> HasWriters (x :: xs)

mutual

  serializeMu : (ts : Vect n Type) -> HasWriters ts -> Mu ts td -> String
  serializeMu ts ws {td} (Inn x) = "(inn " ++ (assert_total $ serialize ((Mu ts td)::ts) ((serializeMu {td} ts ws)::ws) td x) ++ ")"

  serialize : (ts : Vect n Type) -> HasWriters ts -> (t : TDef n) -> (tm : Ty ts t) -> String
  serialize  ts       ws        T1                    ()        = "()"
  serialize  ts       ws        (TSum [x,_])          (Left l)  = "(left "  ++ serialize ts ws x l ++ ")"
  serialize  ts       ws        (TSum [_,y])          (Right r) = "(right " ++ serialize ts ws y r ++ ")"
  serialize  ts       ws        (TSum (x::_::_::_))   (Left l)  = "(left "  ++ serialize ts ws x l ++ ")"
  serialize  ts       ws        (TSum (_::y::z::zs))  (Right r) = "(right " ++ serialize ts ws (TSum (y::z::zs)) r ++ ")"
  serialize  ts       ws        (TProd [x,y])         (a, b)    = "(both "  ++ serialize ts ws x a ++ " " ++ serialize ts ws y b ++ ")"
  serialize  ts       ws        (TProd (x::y::z::zs)) (a, b)    = "(both "  ++ serialize ts ws x a ++ " " ++ serialize ts ws (TProd (y::z::zs)) b ++ ")"
  serialize (_::_)    (w::_)    (TVar FZ)             x         = w x
  serialize (_::_::_) (_::w::_) (TVar (FS FZ))        x         = w x
  serialize (_::ts)   (_::ws)   (TVar (FS (FS i)))    x         = serialize ts ws (TVar (FS i)) x
  serialize ts        ws        (TApp f ys)           x         = assert_total $ serialize ts ws (ap (def f) ys) x
  serialize ts        ws        (TMu td)              (Inn x)   =
    "(inn " ++
      serialize ((Mu ts (args td))::ts) ((serializeMu {td=args td} ts ws)::ws) (args td) x
      ++ ")"
  -- serialize ts        ws        (TName _ td)          x         = serialize ts ws td x
