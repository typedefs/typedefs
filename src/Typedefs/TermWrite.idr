module Typedefs.TermWrite

import Typedefs.Idris
import Typedefs.Names

import Data.Vect

import Data.Bytes
import Data.ByteArray

import Language.JSON

%default total

-- serialization

||| Builds a list that allows to create terms of the given type for each Type in the list of types
public export
data HasGenericWriters : (target : Type) -> (types : Vect n Type) -> Type where
  Nil : HasGenericWriters a Nil
  (::) : (x -> a) -> HasGenericWriters a xs -> HasGenericWriters a (x :: xs)

public export
interface TDefSerialiser target where
  serialise : {n : Nat} -> {ts : Vect n Type} -> HasGenericWriters target ts ->
              (td : TDefR n) -> Ty ts td -> target

public export
TDefSerialiser String where
  serialise  ws        T1                    ()        = "()"
  serialise  ws        (TSum [x,_])          (Left l)  =
    parens $ "left "  ++ serialise ws x l
  serialise  ws        (TSum [_,y])          (Right r) =
    parens $ "right " ++ serialise ws y r
  serialise  ws        (TSum (x::_::_::_))   (Left l)  =
    parens $ "left "  ++ serialise ws x l
  serialise  ws        (TSum (_::y::z::zs))  (Right r) =
    parens $ "right " ++ serialise ws (TSum (y::z::zs)) r
  serialise  ws        (TProd [x,y])         (a, b)    =
    parens $ "both "  ++ serialise ws x a ++ " " ++ serialise ws y b
  serialise  ws        (TProd (x::y::z::zs)) (a, b)    =
    parens $ "both "  ++ serialise ws x a ++ " " ++ serialise ws (TProd (y::z::zs)) b
  serialise {ts=(_::_)}    (w::_)    (RRef FZ)             x         = w x
  serialise {ts=(_::_::_)} (_::w::_) (RRef (FS FZ))        x         = w x
  serialise {ts=(_::ts)}   (_::ws)   (RRef (FS (FS i)))    x         = serialise {ts} ws (TVar (FS i)) x
  serialise {ts=(_::_)}    (w::_)    (TVar FZ)             x         = w x
  serialise {ts=(_::_::_)} (_::w::_) (TVar (FS FZ))        x         = w x
  serialise {ts=(_::ts)}   (_::ws)   (TVar (FS (FS i)))    x         = serialise {ts} ws (TVar (FS i)) x
  serialise ws        (TApp f ys)           x         =
    assert_total $ serialise ws (ap (def f) ys) (convertTy' x)
  serialise ws        (TMu td)              (Inn x) {ts} =
    let inner = assert_total $ serialise {ts=(Mu ts (args td))::ts} (serialise ws (TMu td)::ws) (args td) x in
        "(inn " ++ inner ++ ")"

-- Binary serialisation

serializeInt : {n : Nat} -> (Fin n) -> Bytes
serializeInt x = pack [prim__truncBigInt_B8 (finToInteger x)]

injectionInv : (ts : Vect (2 + k) (TDefR n)) -> Tnary tvars ts Either -> (i : Fin (2 + k) ** Ty tvars (index i ts))
injectionInv [a,b] (Left x) = (0 ** x)
injectionInv [a,b] (Right y) = (1 ** y)
injectionInv (a::b::c::tds) (Left x) = (0 ** x)
injectionInv (a::b::c::tds) (Right y) =
  let (i' ** y') = injectionInv (b::c::tds) y in (FS i' ** y')

public export
TDefSerialiser Bytes where
  serialise ws T0 x impossible
  serialise ws T1 x = empty
  serialise ws (TSum {k = k} tds) x =
     let (i ** x') = injectionInv tds x in
     (serializeInt i) ++ (assert_total $ serialise ws (index i tds) x')
  serialise ws (TProd [a, b]) (x, y) =
    (serialise ws a x) ++ (serialise ws b y)
  serialise ws (TProd (a::b::c::tds)) (x, y) =
    (serialise ws a x) ++ (serialise ws (TProd (b::c::tds))) y
  serialise {ts} ws (TMu tds) (Inn x) =
    assert_total $ serialise {ts=(Mu ts (args tds))::ts}  (serialise ws (TMu tds)::ws) (args tds) x
  serialise {ts=(t::ts)} (w::ws) (TVar FZ) x = w x
  serialise {ts=(t::ts)} (w::ws) {n = S (S n')} (TVar (FS i)) x =
    serialise ws {n = (S n')} (TVar i) x
  serialise {ts=(t::ts)} (w::ws) (RRef FZ) x =  w x
  serialise {ts=(t::ts)} (w::ws) {n = S (S n')} (RRef (FS i)) x =
    serialise ws {n = (S n')} (RRef i) x
  serialise {ts} ws (TApp (TName n d) xs) x =
    assert_total $ serialise ws (ap d xs) (convertTy {n=n} {v=ts} {def=d} {xs=xs} x)

-----------------
-- JSON        --
-----------------


makeFields : Nat -> List String
makeFields n = map (("_" ++) . show) [0 .. n]

mutual
  serialiseJSONMu : HasGenericWriters JSON ts -> Mu ts td -> JSON
  serialiseJSONMu ws {ts} {td} (Inn x) = JObject [("inn",
    (assert_total $ serialiseJSON {ts=((Mu ts td)::ts)} ((serialiseJSONMu ws)::ws) td x))]

  serialiseTNaryProd : HasGenericWriters JSON ts -> (defs: Vect (2 + k) (TDefR n))
                -> Tnary ts defs Pair
                -> List JSON -> List JSON
  serialiseTNaryProd writers [x, y] (a, b) acc =
    [serialiseJSON writers x a, serialiseJSON writers y b]
  serialiseTNaryProd writers (x :: y :: z :: zs) (a , b) acc =
    serialiseJSON writers x a :: serialiseTNaryProd writers (y :: z :: zs) b acc

  serialiseJSON : HasGenericWriters JSON ts -> (t : TDefR n) -> Ty ts t -> JSON
  -- Unit is an empty object
  serialiseJSON x T1 tm = JObject []

  -- Products are serialised as { "_0" : a, "_1" : b, ... , "_x" : n } where the key stands for the
  -- index in the product
  serialiseJSON x (TProd ls) tm = let res = serialiseTNaryProd x ls tm [] in
                                      JObject (zip (makeFields (length ls)) res)
  -- Sums are serialized as { "_x" : term } where x is the index in the sum
  serialiseJSON x (TSum xs) tm =
    let (i ** def) = injectionInv xs tm in
        JObject [("_"++ show (toNat i), assert_total $ serialiseJSON x (index i xs) def)]

  -- Mu are serialised as { "inn" : rec } where rec is the sum associated with a constructor
  serialiseJSON {ts} ws (TMu td) (Inn x) =
      JObject [("inn",  assert_total $
      serialiseJSON {ts=((Mu ts (args td))::ts)} ((serialiseJSONMu {td=args td} ws)::ws) (args td) x)]

  -- TApp applies the tdef to its argument and then serialises the result
  serialiseJSON ws (TApp f ys) tm =
        assert_total $ serialiseJSON ws (ap (def f) ys) (convertTy' tm)

  -- References and variables simply defer to the vector of writers
  serialiseJSON (w::_)    (RRef FZ)          x = w x
  serialiseJSON (_::w::_) (RRef (FS FZ))     x = w x
  serialiseJSON (_::ws)   (RRef (FS (FS i))) x = serialiseJSON ws (RRef (FS i)) x
  serialiseJSON (w::_)    (TVar FZ)          x = w x
  serialiseJSON (_::w::_) (TVar (FS FZ))     x = w x
  serialiseJSON (_::ws)   (TVar (FS (FS i))) x = serialiseJSON ws (TVar (FS i)) x

public export
TDefSerialiser JSON where
  serialise = serialiseJSON
