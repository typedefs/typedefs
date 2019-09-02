module Typedefs.TermWrite

import Typedefs.Typedefs
import Typedefs.Names

import Data.Vect

import Data.Bytes
import Data.ByteArray

%default total
%access public export

-- serialization

data HasWriters : Vect n Type -> Type where
  Nil : HasWriters Nil
  (::) : {xs : Vect n Type} -> (x -> String) -> HasWriters xs -> HasWriters (x :: xs)

mutual

  serializeMu : (ts : Vect n Type) -> HasWriters ts -> Mu ts td -> String
  serializeMu ts ws {td} (Inn x) = "(inn " ++ (assert_total $ serialize ((Mu ts td)::ts) ((serializeMu {td} ts ws)::ws) td x) ++ ")"

  serialize : (ts : Vect n Type) -> HasWriters ts -> (t : TDefR n) -> (tm : Ty ts t) -> String
  serialize  ts       ws        T1                      ()        = "()"
  serialize  ts       ws        (TSum [x,_])            (Left l)  = "(left "  ++ serialize ts ws x l ++ ")"
  serialize  ts       ws        (TSum [_,y])            (Right r) = "(right " ++ serialize ts ws y r ++ ")"
  serialize  ts       ws        (TSum (x::_::_::_))     (Left l)  = "(left "  ++ serialize ts ws x l ++ ")"
  serialize  ts       ws        (TSum (_::y::z::zs))    (Right r) = "(right " ++ serialize ts ws (TSum (y::z::zs)) r ++ ")"
  serialize  ts       ws        (TProd [x,y])           (a, b)    = "(both "  ++ serialize ts ws x a ++ " " ++ serialize ts ws y b ++ ")"
  serialize  ts       ws        (TProd (x::y::z::zs))   (a, b)    = "(both "  ++ serialize ts ws x a ++ " " ++ serialize ts ws (TProd (y::z::zs)) b ++ ")"
  serialize (_::_)    (w::_)    (TVar FZ)               x         = w x
  serialize (_::_::_) (_::w::_) (TVar (FS FZ))          x         = w x
  serialize (_::ts)   (_::ws)   (TVar (FS (FS i)))      x         = serialize ts ws (TVar (FS i)) x
  serialize ts        ws        (TApp (TName _ def) ys) x         = assert_total $ serialize ts ws (ap def ys) (convertTy x)
  serialize ts        ws        (TMu td)                (Inn x)   =
    "(inn " ++
      serialize ((Mu ts (args td))::ts) ((serializeMu {td=args td} ts ws)::ws) (args td) x
      ++ ")"
  serialize (_::_)    (w::_)    (RRef FZ)               x         = w x
  serialize (_::_::_) (_::w::_) (RRef (FS FZ))          x         = w x
  serialize (_::ts)   (_::ws)   (RRef (FS (FS i)))      x         = serialize ts ws (RRef (FS i)) x
  serialize _ _ _ _ = ?speedhack

-- Binary serialisation

Serialiser : Type -> Type
Serialiser a = a -> Bytes

serializeInt : {n : Nat} -> Serialiser (Fin n)
serializeInt x = pack [prim__truncBigInt_B8 (finToInteger x)]

injectionInv : (ts : Vect (2 + k) (TDefR n)) -> Tnary tvars ts Either -> (i : Fin (2 + k) ** Ty tvars (index i ts))
injectionInv [a,b] (Left x) = (0 ** x)
injectionInv [a,b] (Right y) = (1 ** y)
injectionInv (a::b::c::tds) (Left x) = (0 ** x)
injectionInv (a::b::c::tds) (Right y) =
  let (i' ** y') = injectionInv (b::c::tds) y in (FS i' ** y')


serializeBinary : (t : TDefR n) -> (ts : Vect n (a ** Serialiser a)) -> Serialiser (Ty (map DPair.fst ts) t)
serializeBinary T0 ts x impossible
serializeBinary T1 ts x = empty
serializeBinary (TSum {k = k} tds) ts x =
   let (i ** x') = injectionInv tds x in
   (serializeInt i) ++ (assert_total $ serializeBinary (index i tds) ts x')
serializeBinary (TProd [a, b]) ts (x, y) =
  (serializeBinary a ts x) ++ (serializeBinary b ts y)
serializeBinary (TProd (a::b::c::tds)) ts (x, y) =
  (serializeBinary a ts x) ++ (serializeBinary (TProd (b::c::tds))) ts y
serializeBinary (TMu tds) ts (Inn x) = assert_total $  serializeBinary (args tds) ((Mu (map DPair.fst ts) (args tds) ** serializeBinary (TMu tds) ts)::ts) x
serializeBinary (TVar FZ) (t::ts) x = snd t x
serializeBinary {n = S (S n')} (TVar (FS i)) (t::ts) x =
  serializeBinary {n = (S n')} (TVar i) ts x
serializeBinary (TApp (TName _ def) xs) ts x = assert_total $ serializeBinary (ap def xs) ts x
serializeBinary (RRef FZ) (t::ts) x = snd t x
serializeBinary {n = S (S n')} (RRef (FS i)) (t::ts) x =
  serializeBinary {n = (S n')} (RRef i) ts x

serializeBinaryClosed : (t : TDefR 0) -> Serialiser (Ty [] t)
serializeBinaryClosed t = serializeBinary t []
