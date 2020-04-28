module Typedefs.Library

import Data.Vect

import Typedefs.Typedefs
import Typedefs.Names

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
