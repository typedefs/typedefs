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

  cerealiseMu : (ts : Vect n Type) -> HasWriters ts -> Mu ts td -> String
  cerealiseMu ts ws {td} (Inn x) = parens $ "inn " ++
    (assert_total $ cerealise ((Mu ts td)::ts) ((cerealiseMu {td} ts ws)::ws) td x)

  cerealise : (ts : Vect n Type) -> HasWriters ts -> (t : TDefR n) -> (tm : Ty ts t) -> String
  cerealise  ts       ws        T1                    ()        = "()"
  cerealise  ts       ws        (TSum [x,_])          (Left l)  =
    parens $ "left "  ++ cerealise ts ws x l
  cerealise  ts       ws        (TSum [_,y])          (Right r) =
    parens $ "right " ++ cerealise ts ws y r
  cerealise  ts       ws        (TSum (x::_::_::_))   (Left l)  =
    parens $ "left "  ++ cerealise ts ws x l
  cerealise  ts       ws        (TSum (_::y::z::zs))  (Right r) =
    parens $ "right " ++ cerealise ts ws (TSum (y::z::zs)) r
  cerealise  ts       ws        (TProd [x,y])         (a, b)    =
    parens $ "both "  ++ cerealise ts ws x a ++ " " ++ cerealise ts ws y b
  cerealise  ts       ws        (TProd (x::y::z::zs)) (a, b)    =
    parens $ "both "  ++ cerealise ts ws x a ++ " " ++ cerealise ts ws (TProd (y::z::zs)) b
  cerealise (_::_)    (w::_)    (RRef FZ)             x         = w x
  cerealise (_::_::_) (_::w::_) (RRef (FS FZ))        x         = w x
  cerealise (_::ts)   (_::ws)   (RRef (FS (FS i)))    x         = cerealise ts ws (TVar (FS i)) x
  cerealise (_::_)    (w::_)    (TVar FZ)             x         = w x
  cerealise (_::_::_) (_::w::_) (TVar (FS FZ))        x         = w x
  cerealise (_::ts)   (_::ws)   (TVar (FS (FS i)))    x         = cerealise ts ws (TVar (FS i)) x
  cerealise ts        ws        (TApp f ys)           x         =
    assert_total $ cerealise ts ws (ap (def f) ys) (convertTy' x)
  cerealise ts        ws        (TMu td)              (Inn x)   =
    "(inn " ++
      cerealise ((Mu ts (args td))::ts) ((cerealiseMu {td=args td} ts ws)::ws) (args td) x
      ++ ")"

-- Binary cerealisation

Cerealiser : Type -> Type
Cerealiser a = a -> Bytes

cerealiseInt : {n : Nat} -> Cerealiser (Fin n)
cerealiseInt x = pack [prim__truncBigInt_B8 (finToInteger x)]

injectionInv : (ts : Vect (2 + k) (TDefR n)) -> Tnary tvars ts Either -> (i : Fin (2 + k) ** Ty tvars (index i ts))
injectionInv [a,b] (Left x) = (0 ** x)
injectionInv [a,b] (Right y) = (1 ** y)
injectionInv (a::b::c::tds) (Left x) = (0 ** x)
injectionInv (a::b::c::tds) (Right y) =
  let (i' ** y') = injectionInv (b::c::tds) y in (FS i' ** y')

cerealiseBinary : (t : TDefR n) -> (ts : Vect n (a ** Cerealiser a)) -> Cerealiser (Ty (map DPair.fst ts) t)
cerealiseBinary T0 ts x impossible
cerealiseBinary T1 ts x = empty
cerealiseBinary (TSum {k = k} tds) ts x =
   let (i ** x') = injectionInv tds x in
   (cerealiseInt i) ++ (assert_total $ cerealiseBinary (index i tds) ts x')
cerealiseBinary (TProd [a, b]) ts (x, y) =
  (cerealiseBinary a ts x) ++ (cerealiseBinary b ts y)
cerealiseBinary (TProd (a::b::c::tds)) ts (x, y) =
  (cerealiseBinary a ts x) ++ (cerealiseBinary (TProd (b::c::tds))) ts y
cerealiseBinary (TMu tds) ts (Inn x) = assert_total $  cerealiseBinary (args tds) ((Mu (map DPair.fst ts) (args tds) ** cerealiseBinary (TMu tds) ts)::ts) x
cerealiseBinary (TVar FZ) (t::ts) x = snd t x
cerealiseBinary {n = S (S n')} (TVar (FS i)) (t::ts) x =
  cerealiseBinary {n = (S n')} (TVar i) ts x
cerealiseBinary (RRef FZ) (t::ts) x = snd t x
cerealiseBinary {n = S (S n')} (RRef (FS i)) (t::ts) x =
  cerealiseBinary {n = (S n')} (RRef i) ts x
cerealiseBinary (TApp (TName n d) xs) ts x =
  assert_total $ cerealiseBinary (ap d xs) ts (convertTy {n=n} {v=map DPair.fst ts} {def=d} {xs=xs} x)

cerealiseBinaryClosed : (t : TDefR 0) -> Cerealiser (Ty [] t)
cerealiseBinaryClosed t = cerealiseBinary t []
