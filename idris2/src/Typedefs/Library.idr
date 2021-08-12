module Typedefs.Library

import Data.Vect

import Typedefs
import Typedefs.Idris
import Typedefs.Names
import Typedefs.TermWrite
import Typedefs.TermParse

import Language.JSON

%default total

-- BOOL

public export
TBool : TDefR 0
TBool = TSum [T1, T1]

-- NAT

public export
TNat : TDefR 0
TNat = TMu [("Z", T1), ("S", TVar 0)]

public export
TNat1 : TDefR 1
TNat1 = TMu [("Z", T1), ("S", TVar 0)]

public export
toNat : Ty [] TNat -> Nat
toNat (Inn (Left ()))   = Z
toNat (Inn (Right inn)) = S $ toNat inn

public export
fromNat : Nat -> Ty [] TNat
fromNat  Z    = Inn $ Left ()
fromNat (S n) = Inn $ Right $ fromNat n

-- LIST

public export
TList : TDefR 1
TList = TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

public export
TNil : Ty [a] TList
TNil = Inn $ Left ()

public export
TCons : a -> Ty [a] TList -> Ty [a] TList
TCons x xs = Inn $ Right (x, xs)

-- MAYBE

public export
TMaybe : TDefR 1
TMaybe = TMu [("Nothing", T1), ("Just", TVar 1)]

public export
TNothing : Ty [a] TMaybe
TNothing  = Inn $ Left ()

public export
TJust : a -> Ty [a] TMaybe
TJust = Inn . Right

-- EITHER

public export
TEither : TDefR 2
TEither = TMu [("Left", TVar 1), ("Right", TVar 2)]

public export
TLeft : a -> Ty [a,b] TEither
TLeft = Inn . Left

public export
TRight : b -> Ty [a,b] TEither
TRight = Inn . Right

-- PAIR

public export
TPair : TDefR 2
TPair = TProd [TVar 0, TVar 1]

-- STRINGS
public export
TString : TDefR 0
TString = TMu [("String", T0)]

public export
TString1 : TDefR 1
TString1 = TMu [("String", T0)]

-- Numeric

public export
TDouble : TDefR 0
TDouble = TMu [("Double", T0)]

public export
TInt : TDefR 0
TInt = TMu [("Int", T0)]

--------------------------------------------------------------------------------------------------------
-- Specialisations                                                                                    --
---                                                                                                   --
-- There probably is a better way to do this but this will do for now                                 --
--------------------------------------------------------------------------------------------------------

export
StandardIdris : SpecialList 10
StandardIdris = [ (0 ** (TNat, Nat))
                , (0 ** (TString, String))
                , (1 ** (TNat1, const Nat))
                , (1 ** (TString1, const String))
                , (1 ** (TMaybe, Maybe))
                , (2 ** (TEither, Either))
                , (1 ** (TList, List))
                , (0 ** (TBool, Bool))
                , (0 ** (TInt, Int))
                , (0 ** (TDouble, Double))
                ]

writeListJSON : {0 ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect List ts -> JSON
writeListJSON [f] ls = JArray (map f ls)

writeEitherJSON : {0 ts : Vect 2 Type} -> HasGenericWriters JSON ts -> ApplyVect Either ts -> JSON
writeEitherJSON [f, g] (Left l)  = JObject [("Left" , f l)]
writeEitherJSON [f, g] (Right r) = JObject [("Right", g r)]

writeMaybeJSON : {0 ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect Maybe ts -> JSON
writeMaybeJSON [f] y = maybe (JObject []) f y

writeString1JSON : {0 ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect (const String) ts -> JSON
writeString1JSON [_] str = JString str

writeStringJSON : {0 ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect String ts -> JSON
writeStringJSON [] str = JString str

writeNat1JSON : {0 ts : Vect 1 Type} -> HasGenericWriters JSON ts -> ApplyVect (const Nat) ts -> JSON
writeNat1JSON [_] n = JNumber (cast n)

writeNatJSON : {0 ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect Nat ts -> JSON
writeNatJSON [] n = JNumber (cast n)

writeBoolJSON : {0 ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect Bool ts -> JSON
writeBoolJSON [] n = JBoolean n

writeIntJSON : {0 ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect Int ts -> JSON
writeIntJSON [] n = JNumber (cast n)

writeDoubleJSON : {0 ts : Vect 0 Type} -> HasGenericWriters JSON ts -> ApplyVect Double ts -> JSON
writeDoubleJSON [] n = JNumber n

export
StandardContext : HasSpecialisedWriter JSON StandardIdris
StandardContext = [ writeNatJSON
                  , writeStringJSON
                  , writeNat1JSON
                  , writeString1JSON
                  , writeMaybeJSON
                  , writeEitherJSON
                  , writeListJSON
                  , writeBoolJSON
                  , writeIntJSON
                  , writeDoubleJSON
                  ]

parseStringJSON : {n : Nat} -> {0 ts : Vect n Type}
                -> HasParser JSONM JSON ts
                -> SParser JSONM JSON (ApplyVect (ConstN n String) ts)
parseStringJSON {n=Z} [] = MkSParser $ \arg => case arg of
                                               JString n => pure (n, JNull)
                                               _ => Left (MkErr "Expected String")
parseStringJSON {n=S n} (x :: xs) = parseStringJSON {n} xs

parseBoolJSON : {n : Nat} -> {0 ts : Vect n Type}
                -> HasParser JSONM JSON ts
                -> SParser JSONM JSON (ApplyVect (ConstN n Bool) ts)
parseBoolJSON {n=Z} [] = MkSParser $ \arg => case arg of
                                               JBoolean n => pure (n, JNull)
                                               _ => Left (MkErr "Expected Bool")
parseBoolJSON {n=S n} (x :: xs) = parseBoolJSON {n} xs

parseNumericJSON : (numeric : Type) -> Cast Double numeric => {n : Nat} -> {0 ts : Vect n Type}
             -> HasParser JSONM JSON ts
             -> SParser JSONM JSON (ApplyVect (ConstN n numeric) ts)
parseNumericJSON _ {n=Z} [] = MkSParser $ \arg => case arg of
                                             JNumber n => pure (cast n, JNull)
                                             _ => Left (MkErr "Expected Numeric")
parseNumericJSON _ {n=S n} (x :: xs) = parseNumericJSON _ {n} xs

parseMaybeJSON : {0 ts : Vect 1 Type}
              -> HasParser JSONM JSON ts
              -> SParser JSONM JSON (ApplyVect Maybe ts)
parseMaybeJSON [p] = MkSParser $ \arg => case run p arg of
                                              Left err => case arg of
                                                               (JObject []) => Right (Nothing, JNull)
                                                               _ => Left err
                                              Right (v, rest) => Right (Just v, rest)

parseEitherJSON : {0 ts : Vect 2 Type}
               -> HasParser JSONM JSON ts
               -> SParser JSONM JSON (ApplyVect Either ts)
parseEitherJSON [p,q] = ((expectSingleField "Left") *> p)
                  `alt` ((expectSingleField "Right") *>  q)

parseListJSON : {0 ts : Vect 1 Type} -> HasParser JSONM JSON ts -> SParser JSONM JSON (ApplyVect List ts)
parseListJSON [MkSParser p] =
  MkSParser $ \arg =>
    case arg of
         (JArray arr) => let
            f = (map Builtin.fst) . p in flip MkPair JNull <$> traverse f arr
         _  => Left (MkErr "Expected Array")

export
StandardParsers : HasSpecialisedParser JSONM JSON StandardIdris
StandardParsers = [ parseNumericJSON Nat
                  , parseStringJSON
                  , parseNumericJSON Nat {n=1}
                  , parseStringJSON {n=1}
                  , parseMaybeJSON
                  , parseEitherJSON
                  , parseListJSON
                  , parseBoolJSON
                  , parseNumericJSON Int
                  , parseNumericJSON Double]

{-
-}
