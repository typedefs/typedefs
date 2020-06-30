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

TNat1 : TDefR 1
TNat1 = TMu [("Z", T1), ("S", TVar 0)]

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

-- STRINGS
TString : TDefR 0
TString = TMu [("String", T0)]

TString1 : TDefR 1
TString1 = TMu [("String", T0)]

--------------------------------------------------------------------------------------------------------
-- Specialisations                                                                                    --
---                                                                                                   --
-- There probably is a better way to do this but this will do for now                                 --
--------------------------------------------------------------------------------------------------------

StandardIdris : SpecialList 7
StandardIdris = [ (0 ** (TNat, Nat))
                , (0 ** (TString, String))
                , (1 ** (TNat1, const Nat))
                , (1 ** (TString1, const String))
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

writeString1JSON : {ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect (const String) ts -> JSON
writeString1JSON [_] str = JString str

writeStringJSON : {ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect String ts -> JSON
writeStringJSON [] str = JString str

writeNat1JSON : {ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect (const Nat) ts -> JSON
writeNat1JSON [_] n = JNumber (cast n)

writeNatJSON : {ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect Nat ts -> JSON
writeNatJSON [] n = JNumber (cast n)

-- Idk why the compiler gets super confused about `writeNatJSON` (0 arity is the problem?) so you need
-- to explicitly annotate which (::) we need.
StandardContext : HasSpecialisedWriter JSON StandardIdris
StandardContext = SpecialisedWriters.(::) writeNatJSON
                 (SpecialisedWriters.(::) writeStringJSON
                                         [ writeNat1JSON
                                         , writeString1JSON
                                         , writeMaybeJSON
                                         , writeEitherJSON
                                         , writeListJSON
                                         ])

parseString1JSON : {ts : Vect 1 Type} -> HasParser JSONM JSON ts -> (JSON -[JSONM]-> ApplyVect (const String) ts)
parseString1JSON [_] = MkSParser $ \arg => case arg of
                                               JString n => pure (n, JNull)
                                               _ => Left "Expected String"
parseStringJSON : {ts : Vect 0 Type} -> HasParser JSONM JSON ts -> (JSON -[JSONM]-> ApplyVect String ts)
parseStringJSON [] = MkSParser $ \arg => case arg of
                                              JString n => pure (n, JNull)
                                              _ => Left "Expected String"

parseNat1JSON : {ts : Vect 1 Type} -> HasParser JSONM JSON ts -> (JSON -[JSONM]-> ApplyVect (const Nat) ts)
parseNat1JSON [_] = MkSParser $ \arg => case arg of
                                             JNumber n => pure (toNat (cast {to=Int} n), JNull)
                                             _ => Left "Expected Double"

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
StandardParsers = SpecialisedParser.(::) parseNatJSON
                 (SpecialisedParser.(::) parseStringJSON
                                       [ parseNat1JSON
                                       , parseString1JSON
                                       , parseMaybeJSON
                                       , parseEitherJSON
                                       , parseListJSON])

