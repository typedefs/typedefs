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

-- mutual
--   muParser : (ts : Vect n Type) -> All (HasParsers ts :-> Parser' (Mu ts td))
--   muParser {td} ts ps = assert_total $ map (\ty => Inn {tvars = ts} {m = td} ty) $
--                         parens (rand (string "inn")
--                                      (withSpaces $ chooseParser td ((Mu ts td)::ts) ((muParser ts ps)::ps)))

--  chooseParser : (t : TDef n) -> (ts : Vect n Type) -> All (HasParsers ts :-> Parser' (Ty ts t))
--  chooseParser T0                    _         _         = fail
--  chooseParser T1                    _         _         = cmap () $ string "()"
--  chooseParser (TSum [x,y])          ts        ps        =
--    parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts ps))
--                 (rand (string "right") (withSpaces $ chooseParser y ts ps))
--  chooseParser (TSum (x::y::z::zs))  ts        ps        =
--    parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts ps))
--                 (rand (string "right") (withSpaces $ assert_total $ chooseParser (TSum (y::z::zs)) ts ps))
--  chooseParser (TProd [x,y])         ts        ps        =
--    parens $ rand (string "both") (and (withSpaces $ chooseParser x ts ps)
--                                       (withSpaces $ chooseParser y ts ps))
--  chooseParser (TProd (x::y::z::zs)) ts        ps        =
--    parens $ rand (string "both") (and (withSpaces $ chooseParser x ts ps)
--                                       (withSpaces $ assert_total $ chooseParser (TProd (y::z::zs)) ts ps))
--  chooseParser (TVar FZ)             (_::_)    (p::_)    = p
--  chooseParser (TVar (FS FZ))        (_::_::_) (_::p::_) = p
--  chooseParser (TVar (FS (FS i)))    (_::ts)   (_::ps)   = chooseParser (TVar (FS i)) ts ps
--  chooseParser (TApp f xs)           ts        ps        = assert_total $ chooseParser (ap (def f) xs) ts ps
--  chooseParser (TRef n)              ts        ps        = ?imunhappy
--  chooseParser (TMu td)              ts        ps        =
--    map (\ty => Inn {tvars = ts} {m = args td} ty) $
--    parens (rand (string "inn")
--                 (withSpaces $ assert_total $ chooseParser (args td) ((Mu ts (args td))::ts) ((muParser ts ps)::ps)))
  -- chooseParser (TName _ td)          ts        ps        = chooseParser td ts ps

-- this used to depend on chooseParser but now that its gone it is unclear how to proceed
deserialize : (ts : Vect n Type) -> All (HasParsers ts) -> (td : TDefR n) -> String -> Maybe (Ty ts td)
deserialize ts ps td s  = ?deserialize_rhs


-- Binary deserialization

data Deserialiser : Type -> Type where
  MkDeserialiser : (Bytes -> Maybe (a, Bytes)) -> Deserialiser a

runDeserialiser : Deserialiser a -> Bytes -> Maybe (a, Bytes)
runDeserialiser (MkDeserialiser d) = d

Functor Deserialiser where
  map f ma = MkDeserialiser (\ bs => do
    (a', bs') <- runDeserialiser ma bs
    pure (f a', bs'))

Applicative Deserialiser where
  pure x = MkDeserialiser (pure . MkPair x)
  mf <*> ma =  MkDeserialiser (\ bs => do
    (f', bs') <- runDeserialiser mf bs
    (a', bs'') <- runDeserialiser ma bs'
    pure (f' a', bs''))

Monad Deserialiser where
  ma >>= g = MkDeserialiser (\ bs => do
    (a', bs') <- runDeserialiser ma bs
    runDeserialiser (g a') bs')

  join ma = MkDeserialiser (\ bs => do
    (ma', bs') <- runDeserialiser ma bs
    runDeserialiser ma' bs')

fail : Deserialiser a
fail = MkDeserialiser (const Nothing)

-- ||| Interprets the first byte as an Int, and returns the rest of the bytestring, if possible
deserializeInt : (n : Nat) -> Deserialiser (Fin n)
deserializeInt n = MkDeserialiser (\ bs => case (consView bs) of
    Nil => Nothing
    Cons b bs' => map (flip MkPair bs') $ integerToFin (prim__zextB8_BigInt b) n)

injection : (i : Fin (2 + k)) -> (ts : Vect (2 + k) (TDefR n)) -> Ty tvars (index i ts) -> Tnary tvars ts Either
injection FZ      [a, b]             x = Left x
injection (FS FZ) [a, b]             x = Right x
injection FZ     (a :: b :: c :: ts) x = Left x
injection (FS i) (a :: b :: c :: ts) x = Right (injection i (b :: c :: ts) x)

deserializeBinary : (t : TDefR n) -> (ts : Vect n (a ** Deserialiser a)) -> Deserialiser (Ty (map DPair.fst ts) t)
deserializeBinary T0 ts = fail -- will never happen!
deserializeBinary T1 ts = pure ()
deserializeBinary td@(TSum {k = k} tds) ts = do
  i <- deserializeInt (2 + k)
  t' <- deserializeBinary (assert_smaller td (index i tds)) ts
  pure (injection i tds t')
deserializeBinary (TProd [a, b]) ts = do
  ta <- deserializeBinary a ts
  tb <- deserializeBinary b ts
  pure (ta, tb)
deserializeBinary td@(TProd (a ::  b :: c :: tds)) ts = do
  ta <- deserializeBinary a ts
  t' <- deserializeBinary (assert_smaller td (TProd (b :: c :: tds))) ts
  pure (ta, t')
deserializeBinary (TMu tds) ts = do
  t <- assert_total $ deserializeBinary (args tds) ((Mu (map DPair.fst ts) (args tds) ** assert_total $ deserializeBinary (TMu tds) ts)::ts)
  pure (Inn t)
deserializeBinary (TVar FZ) (t::ts) = snd t
deserializeBinary {n = S (S n')} (TVar (FS i)) (t::ts) = deserializeBinary {n = S n'} (TVar i) ts
deserializeBinary (TApp (TName name def) xs) ts = assert_total $ deserializeBinary (ap def xs) (ts)
deserializeBinary (RRef n) ts = fail -- we dont' support reference types

deserializeBinaryClosed : (t : TDefR 0) -> Bytes-> Maybe ((Ty [] t), Bytes)
deserializeBinaryClosed t = runDeserialiser (deserializeBinary t [])
