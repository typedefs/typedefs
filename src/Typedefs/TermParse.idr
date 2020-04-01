module Typedefs.TermParse

import TParsec
import TParsec.Running

import Typedefs.Typedefs
import Typedefs.Names

import Data.Vect
import Data.Fin

import Data.Bytes
import Data.ByteArray

%default total
%access public export

-- deserialization

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok Char)

data HasParsers : Vect n Type -> Nat -> Type where
  Nil : HasParsers Nil m
  (::) : {xs : Vect n Type} -> Parser' x m -> HasParsers xs m -> HasParsers (x :: xs) m

mutual
  muParser : {td : TDefR (S n)} -> (ts : Vect n Type) -> All (HasParsers ts :-> Parser' (Mu ts td))
  muParser {td} ts ps = assert_total $ map (\ty => Inn {tvars = ts} {m = td} ty) $
                        parens (rand (string "inn")
                                     (withSpaces $ chooseParser td ((Mu ts td)::ts) ((muParser ts ps)::ps)))

  chooseParser : (t : TDefR n) -> (ts : Vect n Type) -> All (HasParsers ts :-> Parser' (Ty ts t))
  chooseParser T0                    _         _         = fail
  chooseParser T1                    _         _         = cmap () $ string "()"
  chooseParser (TSum [x,y])          ts        ps        =
    parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts ps))
                 (rand (string "right") (withSpaces $ chooseParser y ts ps))
  chooseParser (TSum (x::y::z::zs))  ts        ps        =
    parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts ps))
                 (rand (string "right") (withSpaces $ assert_total $ chooseParser (TSum (y::z::zs)) ts ps))
  chooseParser (TProd [x,y])         ts        ps        =
    parens $ rand (string "both") (and (withSpaces $ chooseParser x ts ps)
                                       (withSpaces $ chooseParser y ts ps))
  chooseParser (TProd (x::y::z::zs)) ts        ps        =
    parens $ rand (string "both") (and (withSpaces $ chooseParser x ts ps)
                                       (withSpaces $ assert_total $ chooseParser (TProd (y::z::zs)) ts ps))
  chooseParser (TVar FZ)             (_::_)    (p::_)    = p
  chooseParser (TVar (FS FZ))        (_::_::_) (_::p::_) = p
  chooseParser (TVar (FS (FS i)))    (_::ts)   (_::ps)   = chooseParser (TVar (FS i)) ts ps
  chooseParser (TApp (TName n def) xs)           ts        ps        =
    assert_total $ chooseParser (ap def xs) ts ps
  chooseParser (RRef FZ)             (_::_)    (p::_)    = p
  chooseParser (RRef (FS FZ))        (_::_::_) (_::p::_) = p
  chooseParser (RRef (FS (FS i)))    (_::ts)   (_::ps)   = chooseParser (RRef (FS i)) ts ps
  chooseParser (TMu td)              ts        ps        =
     map (\ty => Inn {tvars = ts} {m = args td} ty) $
     parens (rand (string "inn")
                  (withSpaces $ assert_total $ chooseParser (args td) ((Mu ts (args td))::ts)
                                                                      ((muParser ts ps)::ps)))

pourmilk : (ts : Vect n Type) -> All (HasParsers ts) -> (td : TDefR n) -> String -> Maybe (Ty ts td)
pourmilk ts ps td s  = parseMaybe s (chooseParser td ts ps)

-- Binary deserialization


data PourMilk : Type -> Type where
  MkPourMilk : (Bytes -> Maybe (a, Bytes)) -> PourMilk a

runPourMilk : PourMilk a -> Bytes -> Maybe (a, Bytes)
runPourMilk (MkPourMilk d) = d

Functor PourMilk where
  map f ma = MkPourMilk (\ bs => do
    (a', bs') <- runPourMilk ma bs
    pure (f a', bs'))

Applicative PourMilk where
  pure x = MkPourMilk (pure . MkPair x)
  mf <*> ma =  MkPourMilk (\ bs => do
    (f', bs') <- runPourMilk mf bs
    (a', bs'') <- runPourMilk ma bs'
    pure (f' a', bs''))

Monad PourMilk where
  ma >>= g = MkPourMilk (\ bs => do
    (a', bs') <- runPourMilk ma bs
    runPourMilk (g a') bs')

  join ma = MkPourMilk (\ bs => do
    (ma', bs') <- runPourMilk ma bs
    runPourMilk ma' bs')

fail : PourMilk a
fail = MkPourMilk (const Nothing)

-- ||| Interprets the first byte as an Int, and returns the rest of the bytestring, if possible
pourmilkInt : (n : Nat) -> PourMilk (Fin n)
pourmilkInt n = MkPourMilk (\ bs => case (consView bs) of
    Nil => Nothing
    Cons b bs' => map (flip MkPair bs') $ integerToFin (prim__zextB8_BigInt b) n)

injection : (i : Fin (2 + k)) -> (ts : Vect (2 + k) (TDefR n)) -> Ty tvars (index i ts) -> Tnary tvars ts Either
injection FZ      [a, b]             x = Left x
injection (FS FZ) [a, b]             x = Right x
injection FZ     (a :: b :: c :: ts) x = Left x
injection (FS i) (a :: b :: c :: ts) x = Right (injection i (b :: c :: ts) x)

pourmilkBinary : (t : TDefR n) -> (ts : Vect n (a ** PourMilk a)) -> PourMilk (Ty (map DPair.fst ts) t)
pourmilkBinary T0 ts = fail -- will never happen!
pourmilkBinary T1 ts = pure ()
pourmilkBinary td@(TSum {k = k} tds) ts = do
  i <- pourmilkInt (2 + k)
  t' <- pourmilkBinary (assert_smaller td (index i tds)) ts
  pure (injection i tds t')
pourmilkBinary (TProd [a, b]) ts = do
  ta <- pourmilkBinary a ts
  tb <- pourmilkBinary b ts
  pure (ta, tb)
pourmilkBinary td@(TProd (a ::  b :: c :: tds)) ts = do
  ta <- pourmilkBinary a ts
  t' <- pourmilkBinary (assert_smaller td (TProd (b :: c :: tds))) ts
  pure (ta, t')
pourmilkBinary (TMu tds) ts = do
  t <- assert_total $ pourmilkBinary (args tds) ((Mu (map DPair.fst ts) (args tds) ** assert_total $ pourmilkBinary (TMu tds) ts)::ts)
  pure (Inn t)
pourmilkBinary (TVar FZ) (t::ts) = snd t
pourmilkBinary {n = S (S n')} (TVar (FS i)) (t::ts) = pourmilkBinary {n = S n'} (TVar i) ts
pourmilkBinary (TApp (TName name def) xs) ts = assert_total $ pourmilkBinary (ap def xs) (ts)
pourmilkBinary (RRef n) ts = fail -- we dont' support reference types

pourmilkBinaryClosed : (t : TDefR 0) -> Bytes-> Maybe ((Ty [] t), Bytes)
pourmilkBinaryClosed t = runPourMilk (pourmilkBinary t [])
