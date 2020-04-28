module Typedefs.TermWrite

import Typedefs.Typedefs
import Typedefs.Names

import Data.Vect

import Data.Bytes
import Data.ByteArray

import Language.JSON

%default total
%access public export

-- serialization

||| Builds a list that allows to create terms of the given type for each Type in the list of types
data HasGenericWriters : (target : Type) -> (types : Vect n Type) -> Type where
  Nil : HasGenericWriters a Nil
  (::) : {xs : Vect n Type} -> (x -> a) -> HasGenericWriters a xs -> HasGenericWriters a (x :: xs)

mutual
  serializeMu : (ts : Vect n Type) -> HasGenericWriters String ts -> Mu ts td -> String
  serializeMu ts ws {td} (Inn x) = parens $ "inn " ++
    (assert_total $ serialize ((Mu ts td)::ts) ((serializeMu {td} ts ws)::ws) td x)

  serialize : (ts : Vect n Type) -> HasGenericWriters String ts
           -> (t : TDefR n) -> (tm : Ty ts t) -> String
  serialize  ts       ws        T1                    ()        = "()"
  serialize  ts       ws        (TSum [x,_])          (Left l)  =
    parens $ "left "  ++ serialize ts ws x l
  serialize  ts       ws        (TSum [_,y])          (Right r) =
    parens $ "right " ++ serialize ts ws y r
  serialize  ts       ws        (TSum (x::_::_::_))   (Left l)  =
    parens $ "left "  ++ serialize ts ws x l
  serialize  ts       ws        (TSum (_::y::z::zs))  (Right r) =
    parens $ "right " ++ serialize ts ws (TSum (y::z::zs)) r
  serialize  ts       ws        (TProd [x,y])         (a, b)    =
    parens $ "both "  ++ serialize ts ws x a ++ " " ++ serialize ts ws y b
  serialize  ts       ws        (TProd (x::y::z::zs)) (a, b)    =
    parens $ "both "  ++ serialize ts ws x a ++ " " ++ serialize ts ws (TProd (y::z::zs)) b
  serialize (_::_)    (w::_)    (RRef FZ)             x         = w x
  serialize (_::_::_) (_::w::_) (RRef (FS FZ))        x         = w x
  serialize (_::ts)   (_::ws)   (RRef (FS (FS i)))    x         = serialize ts ws (TVar (FS i)) x
  serialize (_::_)    (w::_)    (TVar FZ)             x         = w x
  serialize (_::_::_) (_::w::_) (TVar (FS FZ))        x         = w x
  serialize (_::ts)   (_::ws)   (TVar (FS (FS i)))    x         = serialize ts ws (TVar (FS i)) x
  serialize ts        ws        (TApp f ys)           x         =
    assert_total $ serialize ts ws (ap (def f) ys) (convertTy' x)
  serialize ts        ws        (TMu td)              (Inn x)   =
    "(inn " ++
      serialize ((Mu ts (args td))::ts) ((serializeMu {td=args td} ts ws)::ws) (args td) x
      ++ ")"

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

serializeBinary : (t : TDefR n) -> (ts : Vect n (a ** Serialiser a)) ->
                  Serialiser (Ty (map DPair.fst ts) t)
serializeBinary T0 ts x impossible
serializeBinary T1 ts x = empty
serializeBinary (TSum {k = k} tds) ts x =
   let (i ** x') = injectionInv tds x in
   (serializeInt i) ++ (assert_total $ serializeBinary (index i tds) ts x')
serializeBinary (TProd [a, b]) ts (x, y) =
  (serializeBinary a ts x) ++ (serializeBinary b ts y)
serializeBinary (TProd (a::b::c::tds)) ts (x, y) =
  (serializeBinary a ts x) ++ (serializeBinary (TProd (b::c::tds))) ts y
serializeBinary (TMu tds) ts (Inn x) =
  assert_total $  serializeBinary (args tds) ((Mu (map DPair.fst ts) (args tds) ** serializeBinary (TMu tds) ts)::ts) x
serializeBinary (TVar FZ) (t::ts) x = snd t x
serializeBinary {n = S (S n')} (TVar (FS i)) (t::ts) x =
  serializeBinary {n = (S n')} (TVar i) ts x
serializeBinary (RRef FZ) (t::ts) x = snd t x
serializeBinary {n = S (S n')} (RRef (FS i)) (t::ts) x =
  serializeBinary {n = (S n')} (RRef i) ts x
serializeBinary (TApp (TName n d) xs) ts x =
  assert_total $ serializeBinary (ap d xs) ts (convertTy {n=n} {v=map DPair.fst ts} {def=d} {xs=xs} x)

serializeBinaryClosed : (t : TDefR 0) -> Serialiser (Ty [] t)
serializeBinaryClosed t = serializeBinary t []


HasJSONWriters : Vect n Type -> Type
HasJSONWriters = HasGenericWriters JSON

makeFields : Nat -> List String
makeFields n = map (("_" ++) . show) [0 .. n]

mutual
  serialiseJSONMu : (ts : Vect n Type) -> HasJSONWriters ts -> Mu ts td -> JSON
  serialiseJSONMu ts ws {td} (Inn x) = JObject [("inn",
    (assert_total $ serialiseJSON ((Mu ts td)::ts) ((serialiseJSONMu {td} ts ws)::ws) td x))]

  serialiseTNaryProd : (ts : Vect n Type) -> HasJSONWriters ts -> (defs: Vect (2 + k) (TDefR n))
                -> Tnary ts defs Pair
                -> List JSON -> List JSON
  serialiseTNaryProd types writers [x, y] (a, b) acc =
    [serialiseJSON types writers x a, serialiseJSON types writers y b]
  serialiseTNaryProd types writers (x :: y :: z :: zs) (a , b) acc =
    serialiseJSON types writers x a :: serialiseTNaryProd types writers (y :: z :: zs) b acc

  serialiseJSON : (ts : Vect n Type) -> HasJSONWriters ts ->
                  (t : TDefR n) -> (tm : Ty ts t) -> JSON
  -- Unit is an empty object
  serialiseJSON ts x T1 tm = JObject []

  -- Products are serialised as { "_0" : a, "_1" : b, ... , "_x" : n } where the key stands for the
  -- index in the product
  serialiseJSON ts x (TProd ls) tm = let res = serialiseTNaryProd ts x ls tm [] in
                                         JObject (zip (makeFields (length ls)) res)
  -- Sums are serialized as { "_x" : term } where x is the index in the sum
  serialiseJSON ts x (TSum xs) tm =
    let (i ** def) = injectionInv xs tm in
        JObject [("_"++ show (toNat i), assert_total $ serialiseJSON ts x (index i xs) def)]

  -- Mu are serialised as { "inn" : rec } where rec is the sum associated with a constructor
  serialiseJSON ts ws (TMu td) (Inn x) =
      JObject [("inn",  assert_total $
        serialiseJSON ((Mu ts (args td))::ts) ((serialiseJSONMu {td=args td} ts ws)::ws) (args td) x)]

  -- TApp applies the tdef to its argument and then serialises the result
  serialiseJSON ts ws (TApp f ys) tm =
        assert_total $ serialiseJSON ts ws (ap (def f) ys) (convertTy' tm)

  -- References and variables simply defer to the vector of writers
  serialiseJSON (_::_)    (w::_)    (RRef FZ)          x = w x
  serialiseJSON (_::_::_) (_::w::_) (RRef (FS FZ))     x = w x
  serialiseJSON (_::ts)   (_::ws)   (RRef (FS (FS i))) x = serialiseJSON ts ws (RRef (FS i)) x
  serialiseJSON (_::_)    (w::_)    (TVar FZ)          x = w x
  serialiseJSON (_::_::_) (_::w::_) (TVar (FS FZ))     x = w x
  serialiseJSON (_::ts)   (_::ws)   (TVar (FS (FS i))) x = serialiseJSON ts ws (TVar (FS i)) x
