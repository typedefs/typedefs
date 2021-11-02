module Typedefs.CFT

import Data.List
import Data.Fin
import Data.Maybe
import Data.Nat
import Data.Vect

infixr 1 ~>

record Iso (a, b : Type) where
  constructor MkIso
  to : a -> b
  from : b -> a
  toFrom : (x : b) -> to (from x) === x
  fromTo : (x : a) -> from (to x) === x

namespace Telescope

  public export
  data Tel : Nat -> (f : Nat -> Type) -> Type where
    Nil : Tel 0 f
    (::) : (t : f n) -> Tel n f -> Tel (S n) f

data CFT : Nat -> Type where
  --- variables
  VZ : CFT (S n)
  VS : CFT n -> CFT (S n)

  -- Void
  Zero : CFT n

  -- Unit
  One : CFT n

  -- fixpoint
  Mu : CFT (S n) -> CFT n

  -- Algebraic definitions
  (+) : (a, b : CFT n) -> CFT n
  (*) : (a, b : CFT n) -> CFT n
  -- (~>) : (a, b : CFT n) -> CFT n
  App : CFT (S n) -> CFT n -> CFT n

%inline
µ : CFT (S n) -> CFT n
µ = Mu

var : Fin n -> CFT n
var FZ = VZ
var (FS x) = VS (var x)

-- fromInteger : (x : Integer) -> {n : Nat} ->
--               {auto 0 prf : IsJust (maybeLT (fromInteger x) n)} -> CFT n
-- fromInteger y = var (Data.Fin.fromInteger {n} {prf} y)

data Positive : Integer -> Type where

fromInteger : (x : Integer) -> Positive x => CFT n

interface Universe u where
  El : u -> Type

data Ty : CFT n -> Tel n CFT -> Type where
  Top : Ty t t' -> Ty VZ (t :: t')
  Pop : Ty t t' -> Ty (VS t) (s :: t')
  InL : Ty s t' -> Ty (s + t) t'
  InR : Ty t t' -> Ty (s + t) t'
  Def : Ty f (a :: t) -> Ty (App f a) t
  -- Fun : {k : CFT n} -> (k -> Ty t t') -> Ty (k ~> t) t'
  Void : Ty One t
  Pair : Ty s t' -> Ty t t' -> Ty (s * t) t'
  In : Ty f (Mu f :: t') -> Ty (Mu f) t'

TNat : CFT n
TNat = µ (One + VZ)
-- data Nat = Zero | Succ Nat

TList : CFT (S n)
TList = µ (One + (var 1 * var 0))

TTree : CFT (S n)
TTree = µ (var 1 + (var 0 * var 0))

TRoseTree : CFT (S n)
TRoseTree = µ (var 1 * µ (One + (var 1 * var 0)))

TRoseTree' : CFT (S n)
TRoseTree' = µ (var 1 * App TList (var 0))

zero : Ty TNat t
zero = In (InL Void)

succ : Ty TNat t -> Ty TNat t
succ x = In (InR (Top x))

cons : Ty a t -> Ty TList (a :: t) -> Ty TList (a :: t)
cons x y = In (InR (Pair (Pop (Top x)) (Top y)))

tLen : Ty TList t -> Ty TNat t
tLen (In (InL Void)) = zero
tLen (In (InR (Pair x (Top y)))) = succ (tLen y)

fromNat : Nat -> Ty TNat t
fromNat 0 = zero
fromNat (S k) = succ (fromNat k)

toNat : Ty TNat t -> Nat
toNat (In (InL Void)) = Z
toNat (In (InR (Top x))) = S (toNat x)

plus : (m, n : Ty TNat t ) -> Ty TNat t
plus (In (InL Void)) n = n
plus (In (InR (Top x))) n = succ (plus x n)

namespace Zipper
  public export
  data ZList a = MkZipper (List a) (List a)
  
  moveRight : ZList a -> ZList a
  moveRight ls@(MkZipper xs []) = ls
  moveRight (MkZipper xs (x :: ys)) = MkZipper (x :: xs) ys
  
  moveLeft : ZList a -> ZList a
  moveLeft ls@(MkZipper [] ys) = ls
  moveLeft (MkZipper (x :: xs) ys) = MkZipper xs (x :: ys)
  
  cycleR : ZList a -> ZList a
  cycleR (MkZipper xs []) = MkZipper [] (reverse xs)
  cycleR (MkZipper xs (x :: ys)) = MkZipper (x :: xs) ys

namespace ZipperDescj
  public export
  TZip : CFT (S n)
  TZip = TList * TList 
  
  tMoveRight : Ty TZip (a :: t) -> Ty TZip (a :: t)
  tMoveRight (Pair x (In (InL Void))) = Pair x (In (InL Void))
  tMoveRight (Pair x (In (InR (Pair (Pop (Top y)) (Top z)))))  = Pair (cons y x) z

toList : Ty TList (a :: t) -> List (Ty a t)
toList (In (InL Void)) = []
toList (In (InR (Pair (Pop (Top x)) (Top y)))) = x :: toList y

fromList : List (Ty a t) -> Ty TList (a :: t)
fromList [] = In (InL Void)
fromList (x :: xs) = cons x (fromList xs)

pairInj : (f : Ty TList (a :: t) -> Ty TList (a :: t)) -> fromList (toList y) = y -> CFT.fromList (CFT.toList (f y)) = f y
pairInj f prf = ?pairInj_rhs

toFromList : (x : Ty (Mu (One + (VS VZ * VZ))) (a :: t)) -> fromList (toList x) = x
toFromList (In (InL Void)) = Refl
toFromList (In (InR (Pair x (Top y)))) = let result = toFromList y in 
                                             pairInj (In . InR . Pair x . Top) result

fromToList : (x : List (Ty a t)) -> CFT.toList (fromList x) = x
fromToList [] = Refl
fromToList (x :: xs) = let rec = fromToList xs in cong (x :: ) rec

ListTListIso : Iso (List (Ty a t)) (Ty TList (a :: t))
ListTListIso = MkIso
  { to = fromList
  , from = toList
  , toFrom = toFromList
  , fromTo = fromToList
  }


fromZList : ZList (Ty a t) -> Ty TZip (a :: t)
fromZList (MkZipper xs ys) = Pair (fromList xs) (fromList ys)

toZList : Ty TZip (a :: t) -> ZList (Ty a t) 
toZList (Pair x y) = MkZipper (toList x) (toList y) 

toFromZList : (x : Ty TZip (a :: t)) -> fromZList (toZList x) = x
toFromZList (Pair x y) = ?toFromZList_rhs_1

ZListTZipIso : Iso (ZList (Ty a t)) (Ty TZip (a :: t))
ZListTZipIso = MkIso 
  { to = fromZList
  , from = toZList
  , toFrom = toFromZList
  , fromTo = ?aiod
  }


data Morph : (s, t : Tel n f) -> Type where

    ML : Morph s s

    MF : (f : Ty s s' -> Ty t t')
      -> (phi : Morph s' t')
      ----------------------------
      -> Morph (s :: s') (t :: t')

    Mµ : Morph s' t' -> Morph (t :: s') (t :: t')

gMap : Morph s' t' -> Ty t s' -> Ty t t'
gMap ML         (Top x) = Top x
gMap (MF f phi) (Top x) = Top (f x)
gMap (Mµ phi)   (Top x) = Top (gMap phi x)
gMap ML         (Pop x) = Pop x
gMap (MF f phi) (Pop x) = Pop (gMap phi x)
gMap (Mµ phi)   (Pop x) = Pop (gMap phi x)
gMap phi        (InL x) = InL (gMap phi x)
gMap phi        (InR x) = InR (gMap phi x)
gMap phi        (Def x) = Def (gMap (Mµ phi) x)
gMap phi        Void = Void
gMap phi        (Pair x y) = Pair (gMap phi x) (gMap phi y)
gMap phi        (In x) = In (gMap (Mµ phi) x)

record DepLens (s, a : Type) (t : s -> Type) (b : a -> Type) where
  constructor MkDepLens
  get : s -> a
  set : (es : s) -> b (get es) -> t es

-- deriveLenses : {a, b, s, t : CFT n} -> Lens (Ty a t') (Ty b t') (Ty s t') (Ty t t') ->

derive : Fin n -> CFT n -> CFT n
derive FZ     VZ = One
derive (FS x) VZ = Zero
derive FZ     (VS y) = Zero
derive (FS x) (VS y) = Zero
derive n      (App f x) = App (derive (FS n) f) x
                        + App (derive FZ f) x * derive n x
derive n      Zero = Zero
derive n      One = Zero
derive n      (a + b) = derive n a + derive n b
derive n      (a * b) = derive n a * b + a * derive n b
derive n      (Mu f) = App TList (App (derive FZ f) (Mu f))
                     * App (derive (FS n) f) (Mu f)

DerivedList : CFT 1
DerivedList = derive FZ TList

Path : CFT (S n) -> CFT n
Path f = App TList (App (derive FZ f) (Mu f))

record SCont (n : Nat) where
    constructor MkSCont
    shapes : Type
    seq : (x, y : shapes) -> Dec (x = y)
    positions : Fin n -> shapes -> Nat

SExt : {n : Nat} -> SCont n -> Vect n Type -> Type
SExt (MkSCont shapes seq pos) x =
    DPair shapes (\s => ((i : Fin n) -> (Vect (pos i s) (index i x))))


-- ex : {n : Nat} -> String
-- ex {n} = "hello" ++ show n
-- 
-- 
-- main : IO ()
-- main = putStrLn ex
