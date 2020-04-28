module Typedefs.TermParse

import TParsec
import TParsec.Running

import Typedefs.Typedefs
import Typedefs.Names

import Data.Vect
import Data.Fin
import Data.String

import Data.Bytes
import Data.ByteArray

import Language.JSON

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

deserialise : (ts : Vect n Type) -> All (HasParsers ts) -> (td : TDefR n) -> String -> Maybe (Ty ts td)
deserialise ts ps td s  = parseMaybe s (chooseParser td ts ps)

-- Binary deserialization


data GenericDeserialiser : Type -> Type -> Type where
  MkGenericDeserialiser : (b -> Maybe (a, b)) -> GenericDeserialiser b a

Deserialiser : Type -> Type
Deserialiser = GenericDeserialiser Bytes

runDeserialiser : GenericDeserialiser b a -> b -> Maybe (a, b)
runDeserialiser (MkGenericDeserialiser d) = d

Functor (GenericDeserialiser a) where
  map f ma = MkGenericDeserialiser (\ bs => do
    (a', bs') <- runDeserialiser ma bs
    pure (f a', bs'))

Applicative (GenericDeserialiser b) where
  pure x = MkGenericDeserialiser (pure . MkPair x)
  mf <*> ma =  MkGenericDeserialiser (\ bs => do
    (f', bs') <- runDeserialiser mf bs
    (a', bs'') <- runDeserialiser ma bs'
    pure (f' a', bs''))

Monad (GenericDeserialiser b) where
  ma >>= g = MkGenericDeserialiser (\ bs => do
    (a', bs') <- runDeserialiser ma bs
    runDeserialiser (g a') bs')

  join ma = MkGenericDeserialiser (\ bs => do
    (ma', bs') <- runDeserialiser ma bs
    runDeserialiser ma' bs')

fail : GenericDeserialiser b a
fail = MkGenericDeserialiser (const Nothing)

-- ||| Interprets the first byte as an Int, and returns the rest of the bytestring, if possible
deserialiseInt : (n : Nat) -> Deserialiser (Fin n)
deserialiseInt n = MkGenericDeserialiser (\ bs => case (consView bs) of
    Nil => Nothing
    Cons b bs' => map (flip MkPair bs') $ integerToFin (prim__zextB8_BigInt b) n)

injection : (i : Fin (2 + k)) -> (ts : Vect (2 + k) (TDefR n)) -> Ty tvars (index i ts) -> Tnary tvars ts Either
injection FZ      [a, b]             x = Left x
injection (FS FZ) [a, b]             x = Right x
injection FZ     (a :: b :: c :: ts) x = Left x
injection (FS i) (a :: b :: c :: ts) x = Right (injection i (b :: c :: ts) x)

deserialiseBinary : (t : TDefR n) -> (ts : Vect n (a ** Deserialiser a)) -> Deserialiser (Ty (map DPair.fst ts) t)
deserialiseBinary T0 ts = fail -- will never happen!
deserialiseBinary T1 ts = pure ()
deserialiseBinary td@(TSum {k = k} tds) ts = do
  i <- deserialiseInt (2 + k)
  t' <- deserialiseBinary (assert_smaller td (index i tds)) ts
  pure (injection i tds t')
deserialiseBinary (TProd [a, b]) ts = do
  ta <- deserialiseBinary a ts
  tb <- deserialiseBinary b ts
  pure (ta, tb)
deserialiseBinary td@(TProd (a ::  b :: c :: tds)) ts = do
  ta <- deserialiseBinary a ts
  t' <- deserialiseBinary (assert_smaller td (TProd (b :: c :: tds))) ts
  pure (ta, t')
deserialiseBinary (TMu tds) ts = do
  t <- assert_total $ deserialiseBinary (args tds) ((Mu (map DPair.fst ts) (args tds) ** assert_total $ deserialiseBinary (TMu tds) ts)::ts)
  pure (Inn t)
deserialiseBinary (TVar FZ) (t::ts) = snd t
deserialiseBinary {n = S (S n')} (TVar (FS i)) (t::ts) = deserialiseBinary {n = S n'} (TVar i) ts
deserialiseBinary (TApp (TName name def) xs) ts = assert_total $ deserialiseBinary (ap def xs) (ts)
deserialiseBinary (RRef n) ts = fail -- we dont' support reference types

deserialiseBinaryClosed : (t : TDefR 0) -> Bytes-> Maybe ((Ty [] t), Bytes)
deserialiseBinaryClosed t = runDeserialiser (deserialiseBinary t [])


JSONM : Type -> Type
JSONM = Either String

parseObject : JSON -> JSONM (List (String, JSON))
parseObject (JObject ls) = pure ls
parseObject _ = Left "expected Object"

parseInt : JSON -> JSONM Int
parseInt (JNumber n) = pure (cast n)
parseInt _ = Left "expected Int"

-- check if the key starts with an underscore and if its smaller than 2 + k
parseKey : String -> JSONM (Fin (2 + k))
parseKey "" = Left "Invalid key: empty"
parseKey str {k} = do '_' <- safeHead str | Left ("Invalid key: '" ++ str ++ "'")
                      rest <- safeTail str
                      let i = parsePositive rest
                      index <- (maybeToEither "Invalid key" i)
                      maybeToEither "Invalid Key" $ natToFin index (2 + k)
    where
      safeStrOp : (String -> a) -> String -> JSONM a
      safeStrOp op str = if length str > 0 then pure (op str)
                                           else Left "expected index"
      safeHead : String -> JSONM Char
      safeHead = assert_total $ safeStrOp strHead
      safeTail : String -> JSONM String
      safeTail = assert_total $ safeStrOp strTail



injProd : (vec : Vect (2 + k) (ts : TDefR n ** Ty tds ts))
       -> Tnary tds (map DPair.fst vec) Pair
injProd [(_ ** x), (_ ** y)] = (x, y)
injProd ((_ ** x) :: y :: z :: zs) = (x, assert_total $ injProd (y :: z :: zs))

-- we need to check all keys are in increasing order and of the format _X from 0 to l
parseVect : List (String, JSON) -> (l : Nat) -> JSONM (Vect l JSON)
parseVect ls n = case decEq (length ls) n of
                      Yes prf => rewrite sym prf in pure $ map snd (fromList ls)
                      No _ => Left ("incompatible lengths: " ++ show (length ls)
                                    ++ " and " ++ show n)

deserialiseJSON : (t : TDefR n) -> (ts : Vect n (a ** (JSON -> JSONM a)))
               -> JSON -> Either String (Ty (map DPair.fst ts) t)
deserialiseJSON T0 ts json = Left "parsing 0"
deserialiseJSON T1 ts json = pure ()
deserialiseJSON td@(TSum {k = k} tds) ts json =  do
  [(key, obj)] <- parseObject json
    | _ => Left "Object doens't contain exactly 1 element"
  key' <- parseKey key
  t' <- deserialiseJSON (assert_smaller td (index key' tds)) ts obj
  pure $ injection key' tds t'
deserialiseJSON (TProd products {k}) ts json {n} = do
  keyValues <- parseObject json
  vec <- parseVect keyValues (2 + k)
  res <- the (JSONM $ Vect (2 + k) (td : TDefR n ** Ty (map DPair.fst ts) td))
             (traverse (\(def, j) => MkDPair def <$> (assert_total $ deserialiseJSON def ts j))
                       (zip products vec))
  -- Alright explaination time:
  --
  -- In the previous line we compute a vector of parsed JSON along with the TDef they are supposed
  -- to be a member of. This dependent pair comes from zipping `products` and the vector of JSONs
  -- and then traversing it while parsing the jsons using the TDefs as a schema to say "here is
  -- the expected type this value shoud parse as".
  -- However in order to return the Idris type associated with this product type we need a proof
  -- that the values we parsed (and their type) correspond to the types we expect from `products`
  -- (which itself is the vector of TDefs that  defines which types we expect in which order).
  --
  -- But now we're stuck because we have a vector of (def : TDefR n ** f def) where the first
  -- projection _is_ the TDef from `products` (because we zipped them and took the first element to
  -- make the returning DPair), but we don't have a proof of it.
  --
  -- I tried using `let prf = the (map fst res = products) (believe_me Refl)` and rewriting but
  -- it just wouldn't work. In the end, since as a programmer I _know_ this is true because of the
  -- implementation, I decided to force the hand of the compiler and use `belive_me` at the call
  -- site of `injprod` (which builds the Idris value from the given product) rather than in a
  -- rewrite. This is safe but dangerous if we ever change the line right above this scary comment.
  --
  -- Please don't ignore this comment when you change the code around those two lines.
  pure $ believe_me $ injProd res
deserialiseJSON (TMu tds) ts json = do
  [("inn", val)] <- parseObject json
    | [] => Left "Expected inner mu but object was empty"
    | ls => Left ("Expected exactly one inner mu value, got " ++ (show $ ls))

  parsed <- assert_total (deserialiseJSON
              (args tds)
              ((Mu (map DPair.fst ts) (args tds) ** assert_total $ deserialiseJSON (TMu tds) ts)::ts)
              val)
  pure (Inn parsed)
deserialiseJSON (TVar FZ) ((_ ** t)::ts) json = t json
deserialiseJSON {n = S (S n')} (TVar (FS i)) ((_ ** t)::ts) json =
  deserialiseJSON {n = S n'} (TVar i) ts json
deserialiseJSON (TApp (TName name def) xs) ts json = assert_total $ deserialiseJSON (ap def xs) (ts) json
deserialiseJSON (RRef FZ) ((_ ** t)::ts) json = t json
deserialiseJSON {n = S (S n')} (RRef (FS i)) ((_ ** t)::ts) json =
  deserialiseJSON {n = S n'} (RRef i) ts json

