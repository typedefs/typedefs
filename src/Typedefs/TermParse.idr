module Typedefs.TermParse

import TParsec
import TParsec.Running

import Typedefs.Idris

import Data.Vect
import Data.Fin
import Data.String

import Data.Bytes
import Data.ByteArray

import Language.JSON

%default total
%access public export

---------------------------------------------------------------------------------------------
-- Parser & Interfaces                                                                     --
---------------------------------------------------------------------------------------------

-- A simple Parser, a wrapper for a parsing function `a -> m (b, a)`
data SParser : (Type -> Type) -> Type -> Type -> Type where
  MkSParser : Monad m => (source -> m (target, source)) -> SParser m source target

-- Special syntax for a parser using monad `m`
syntax [a] "-[" [m] "]->" [b] = SParser m a b

run : (src -[m]-> trg) -> src -> m (trg, src)
run (MkSParser p) = p

runParser : (Functor m) => (src -[m]-> trg) -> src -> m trg
runParser (MkSParser p) s = Basics.fst <$> p s

||| A proof that each type variable has a suitable parser
data HasParser : (Type -> Type) -> (format : Type) -> Vect n Type -> Type where
  Nil : HasParser m format []
  (::) : Monad m => (src -[m]-> trg) -> HasParser m src ts -> HasParser m src (trg :: ts)

Monad m => Functor (SParser m s) where
  map f (MkSParser ma) = MkSParser $ \bs => do
    (a', bs') <- ma bs
    pure (f a', bs')

Monad m => Applicative (SParser m s) where
  pure x = MkSParser (pure . MkPair x)

  (<*>) (MkSParser mf) (MkSParser ma) = MkSParser $ \bs => do
      (f', bs') <- mf bs
      (a', bs'') <- ma bs'
      pure (f' a', bs'')

Monad m => Monad (SParser m s) where
  (>>=) (MkSParser ma) g = MkSParser $ \bs => do
      (a', bs') <- ma bs
      run (g a') bs'

injection : (i : Fin (2 + k)) -> (ts : Vect (2 + k) (TDefR n)) -> Ty tvars (index i ts) -> Tnary tvars ts Either
injection FZ      [a, b]             x = Left x
injection (FS FZ) [a, b]             x = Right x
injection FZ     (a :: b :: c :: ts) x = Left x
injection (FS i) (a :: b :: c :: ts) x = Right (injection i (b :: c :: ts) x)

failParser : Monad m => (error : m Void) -> s -[m]-> Void
failParser error = MkSParser $ \arg => void <$> error

getVar : {vs : Vect n Type} -> (i : Fin n) ->  HasParser m format vs -> (format -[m]-> index i vs)
getVar FZ (p::ps) = p
getVar {n = S (S n')} (FS i) (p::ps) =
  getVar {n = S n'} i ps


public export
interface (Monad m) => TDefDeserialiser (m : Type -> Type) format where

  voidError : m Void

  parseProd : {ts : Vect n Type} -> HasParser m format ts -> (args : Vect (2 + k) (TDefR n)) ->
             (format -[m]-> (Ty ts (TProd args)))

  parseSum : {ts : Vect n Type} -> HasParser m format ts -> (args : Vect (2 + k) (TDefR n)) ->
             (format -[m]-> (Ty ts (TSum args)))

  parseMu : format -[m]-> ()
  parseMu = MkSParser $ pure . MkPair ()

deserialiser : {m : Type -> Type} -> {format : Type} -> (TDefDeserialiser m format) =>
               {ts : Vect n Type} -> HasParser m format ts ->
               (td : TDefR n) -> (format -[m]-> (Ty ts td))
deserialiser ps T0 = failParser (voidError {m} {format})
deserialiser ps T1 = pure ()
deserialiser ps (TSum {k = k} tds) = parseSum ps tds
deserialiser ps (TProd products {k}) = parseProd ps products
deserialiser ps (TMu tds) {ts} = do
  () <- parseMu
  let muParser = assert_total $ deserialiser ps (TMu tds)
  parsed <- assert_total $ deserialiser (muParser :: ps) (args tds)
  pure (Inn parsed)
deserialiser p (TVar i) = getVar i p
deserialiser p (RRef i) = getVar i p
deserialiser ps (TApp (TName name def) xs) = assert_total $ deserialiser ps (ap def xs)


export
deserialise : (Monad m, TDefDeserialiser m format) =>  {ts : Vect n Type} ->
              HasParser m format ts -> (td : TDefR n) ->
              format -> m (Ty ts td)
deserialise ps td = TermParse.runParser $ deserialiser ps td

---------------------------------------------------------------------------------------------
-- Strings                                                                                 --
----                                                                                       --
-- The string parser is different so we leave it in its own namespace without implementing --
-- the common TDefDeserialiser interface.                                                  --
---------------------------------------------------------------------------------------------

namespace StringParser
  Parser' : Type -> Nat -> Type
  Parser' = Parser TParsecU (sizedtok Char)

  data StringParsers : Vect n Type -> Nat -> Type where
    Nil : StringParsers Nil m
    (::) : {xs : Vect n Type} -> Parser' x m -> StringParsers xs m -> StringParsers (x :: xs) m

  mutual
    muParser : {td : TDefR (S n)} -> (ts : Vect n Type) -> All (StringParsers ts :-> Parser' (Mu ts td))
    muParser {td} ts ps = assert_total $ map (\ty => Inn' {tvars = ts} {m = td} ty) $
                          parens (rand (string "inn")
                                       (withSpaces $ chooseParser td ((Mu ts td)::ts) ((muParser ts ps)::ps)))

    chooseParser : (t : TDefR n) -> (ts : Vect n Type) -> All (StringParsers ts :-> Parser' (Ty ts t))
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
       map (\ty => Inn' {tvars = ts} {m = args td} ty) $
       parens (rand (string "inn")
                    (withSpaces $ assert_total $ chooseParser (args td) ((Mu ts (args td))::ts)
                                                                        ((muParser ts ps)::ps)))

  deserialiseStr : {ts : Vect n Type} -> All (StringParsers ts) -> (td : TDefR n) -> String -> Maybe (Ty ts td)
  deserialiseStr {ts} ps td s  = parseMaybe s (chooseParser td ts ps)

---------------------------------------------------------------------------------------------
-- Binary                                                                                  --
---------------------------------------------------------------------------------------------

fail : s -[Maybe]-> a
fail = MkSParser $ const Nothing

||| Interprets the first byte as an Int, and returns the rest of the bytestring, if possible
deserialiseInt : (n : Nat) -> (Bytes -[Maybe]-> (Fin n))
deserialiseInt n = MkSParser $ \bs => case (consView bs) of
    Nil => Nothing
    Cons b bs' => flip MkPair bs' <$> integerToFin (prim__zextB8_BigInt b) n

export
TDefDeserialiser Maybe Bytes where

  voidError = Nothing

  parseSum ps tds {k} = do
    i <- deserialiseInt (2 + k)
    t' <- assert_total $ deserialiser ps (index i tds)
    pure (injection i tds t')

  parseProd ps [a,b] = do
    ta <- assert_total $ deserialiser ps a
    tb <- assert_total $ deserialiser ps b
    pure (ta, tb)

  parseProd ps (a :: b :: c :: tds) = do
    ta <- assert_total $ deserialiser ps a
    t' <- assert_total $ deserialiser ps (TProd (b :: c :: tds))
    pure (ta, t')

---------------------------------------------------------------------------------------------
-- JSON                                                                                    --
---------------------------------------------------------------------------------------------

||| Errors when parsing JSON
JSONM : Type -> Type
JSONM = Either String

||| Type of parsers that consume JSON
JParser : Type -> Type
JParser = SParser (Either String) JSON

||| Expect JSON is an object and return its fields
parseObject : JParser (List (String, JSON))
parseObject = MkSParser parse
  where
    parse : JSON -> JSONM ((List (String, JSON)), JSON)
    parse (JObject ls) = Right (ls, JNull)
    parse _ = Left "expected Object"

||| Expects JSON is an integer value
parseInt : JParser Int
parseInt = MkSParser parse
  where
    parse : JSON -> JSONM (Int, JSON)
    parse (JNumber n) = pure ((cast n), JNull)
    parse _ = Left "expected Int"

||| check if the key starts with an underscore and if its smaller than 2 + k
parseKey : (k : Nat) -> String -> JSONM (Fin (2 + k))
parseKey k "" = Left "Invalid key: empty"
parseKey k str = do '_' <- safeHead str | Left ("Invalid key: '" ++ str ++ "'")
                    rest <- safeTail str
                    let i = parsePositive rest
                    index <- maybeToEither "Invalid key" i
                    maybeToEither "Invalid Key" $ natToFin index (2 + k)
    where
      safeStrOp : (String -> a) -> String -> JSONM a
      safeStrOp op str = if length str > 0 then Right (op str)
                                           else Left "expected index"
      safeHead : String -> JSONM Char
      safeHead = assert_total $ safeStrOp strHead
      safeTail : String -> JSONM String
      safeTail = assert_total $ safeStrOp strTail

namespace ParseProduct
  ||| A proof that each element of a product has been successfully parsed
  data ParseProd : Vect n Type -> Vect l (TDefR n) -> Type where
    Nil : ParseProd vs []
    (::) : {td : TDefR n} -> (parsed : Ty vs td) -> ParseProd vs ts -> ParseProd vs (td::ts)

injProd : {vs : Vect n Type} -> {vec : Vect (2 + k) (TDefR n)} -> ParseProd vs vec
       -> Tnary vs vec Pair
injProd [a, b] = (a, b)
injProd (a :: b :: x :: xs) = (a , injProd (b :: x :: xs))

jsonFail : String -> SParser JSONM a b
jsonFail str = MkSParser (const $ Left str)

-- we need to check all keys are in increasing order and of the format _X from 0 to l
parseVect : List (String, JSON) -> (l : Nat) -> JSONM (Vect l JSON)
parseVect ls n = case decEq (length ls) n of
                      Yes prf => rewrite sym prf in Applicative.pure $ Functor.map snd (fromList ls)
                      No _ => Left ("incompatible lengths: " ++ show (length ls)
                                    ++ " and " ++ show n)

||| Lift a function into a parser that operates on the value but does not consume it
liftParse : Monad m => {a : Type} -> (a -> m b) -> (a -[m]-> b)
liftParse f = MkSParser (\v => flip MkPair v <$> f v)

liftVal : Monad m => m b -> (a -[m]-> b)
liftVal v = liftParse (const v)

||| Parses an object with a single field. Returns the parsed key and the json as leftover
parseSingleObject : JParser String
parseSingleObject = do
    [v] <- parseObject
        | jsonFail "Object doens't contain exactly 1 element"
    MkSParser (const $ pure v)

export
TDefDeserialiser (Either String) JSON where

  voidError = Left "parsing Void"

  -- mu is an object with a single field called "inn"
  parseMu = do
    "inn" <- parseSingleObject
      | jsonFail "Expected exactly one inner mu value"
    pure ()

  parseSum ps tds {k} = do
    key <- parseSingleObject
    let (Right key') = parseKey k key
      | Left err => jsonFail err
    t' <- assert_total $ deserialiser ps (index key' tds)
    pure (injection key' tds t')

  parseProd ps tds {n} {k} {ts} = do
      keyValues <- parseObject
      vec <- liftVal $ parseVect keyValues (2 + k)
      res <- liftVal $ toParsedProd tds vec
      pure $ injProd res
    where
      toParsedProd : (tds : Vect l (TDefR n)) -> Vect l JSON -> JSONM (ParseProd ts tds)
      toParsedProd [] [] {l = Z} = pure []
      toParsedProd (t::tds) (j::js) {l = (S k)} = do
        r <- runParser (assert_total $ deserialiser ps t) j
        rs <- toParsedProd tds js
        pure $ r :: rs


