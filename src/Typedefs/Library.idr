module Typedefs.Library

import Data.Vect

import Typedefs.Idris
import Typedefs.Names
import Typedefs.TermWrite
import Typedefs.TermParse

import Language.JSON

%default total
%access public export

-- NAT

TNat : TDefR 0
TNat = TMu [("Z", T1), ("S", TVar 0)]

toNat : Ty [] TNat -> Nat
toNat (Inn (Left ()))   = Z
toNat (Inn (Right inn)) = S $ toNat inn

fromNat : Nat -> Ty [] TNat
fromNat  Z    = Inn $ Left ()
fromNat (S n) = Inn $ Right $ fromNat n

-- LIST

TList : TDefR 1
TList = TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

TNil : Ty [a] TList
TNil = Inn $ Left ()

TCons : a -> Ty [a] TList -> Ty [a] TList
TCons x xs = Inn $ Right (x, xs)

toList : Ty [] (TList `ap` [tdef]) -> List (Ty [] tdef)
toList (Inn (Left ()))        = Nil
toList (Inn (Right (hd, tl))) = ignoreShift hd :: toList tl

fromList : List (Ty [] tdef) -> Ty [] (TList `ap` [tdef])
fromList  Nil      = Inn (Left ())
fromList (x :: xs) = Inn (Right (addShift x, fromList xs))

-- MAYBE

TMaybe : TDefR 1
TMaybe = TMu [("Nothing", T1), ("Just", TVar 1)]

TNothing : Ty [a] TMaybe
TNothing  = Inn $ Left ()

TJust : a -> Ty [a] TMaybe
TJust = Inn . Right

-- EITHER

TEither : TDefR 2
TEither = TMu [("Left", TVar 1), ("Right", TVar 2)]

TLeft : a -> Ty [a,b] TEither
TLeft = Inn . Left

TRight : b -> Ty [a,b] TEither
TRight = Inn . Right

-- PAIR

TPair : TDefR 2
TPair = TProd [TVar 0, TVar 1]

--------------------------------------------------------------------------------------------------------
-- Specialisations                                                                                    --
---                                                                                                   --
-- There probably is a better way to do this but this will do for now                                 --
--------------------------------------------------------------------------------------------------------

StandardIdris : SpecialList 4
StandardIdris = [ (0 ** (TNat, Nat))
                , (1 ** (TMaybe, Maybe))
                , (2 ** (TEither, Either))
                , (1 ** (TList, List))
                ]

writeListJSON : {ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect List ts -> JSON
writeListJSON [f] ls = JArray (map f ls)

writeEitherJSON : {ts : Vect 2 Type} -> HasGenericWriters JSON ts -> ApplyVect Either ts -> JSON
writeEitherJSON [f, g] (Left l)  = JObject [("Left" , f l)]
writeEitherJSON [f, g] (Right r) = JObject [("Right", g r)]

writeMaybeJSON : {ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect Maybe ts -> JSON
writeMaybeJSON [f] y = maybe (JObject []) f y

writeNatJSON : {ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect Nat ts -> JSON
writeNatJSON [] n = JNumber (cast n)

-- Idk why the compiler gets super confused about `writeNatJSON` (0 arity is the problem?) so you need
-- to explicitly annotate which (::) we need.
StandardContext : HasSpecialisedWriter JSON StandardIdris
StandardContext = SpecialisedWriters.(::) writeNatJSON [writeMaybeJSON, writeEitherJSON, writeListJSON]

parseNatJSON : {ts : Vect 0 Type} -> HasParser JSONM JSON ts -> (JSON -[JSONM]-> ApplyVect Nat ts)
parseNatJSON [] = MkSParser $ \arg => case arg of
                                           JNumber n => pure (toNat (cast {to=Int} n), JNull)
                                           _ => Left "Expected Double"

parseMaybeJSON : {ts : Vect 1 Type} -> HasParser JSONM JSON ts -> JSON -[JSONM]-> ApplyVect Maybe ts
parseMaybeJSON [p] = MkSParser $ \arg => case run p arg of
                                              Left err => case arg of
                                                               (JObject []) => Right (Nothing, JNull)
                                                               _ => Left err
                                              Right (v, rest) => Right (Just v, rest)

parseEitherJSON : {ts : Vect 2 Type} -> HasParser JSONM JSON ts -> JSON -[JSONM]-> ApplyVect Either ts
parseEitherJSON [p,q] = ((expectSingleField "Left") >>= const p)
                  `alt` ((expectSingleField "Right") >>= const q)

parseListJSON : {ts : Vect 1 Type} -> HasParser JSONM JSON ts -> JSON -[JSONM]-> ApplyVect List ts
parseListJSON [MkSParser p] =
  MkSParser $ \arg =>
    case arg of
         (JArray arr) => let
            f = (map Basics.fst) . p in flip MkPair JNull <$> traverse f arr
         _  => Left "Expected Array"

StandardParsers : HasSpecialisedParser JSONM JSON StandardIdris
StandardParsers = SpecialisedParser.(::) parseNatJSON [parseMaybeJSON, parseEitherJSON, parseListJSON]

