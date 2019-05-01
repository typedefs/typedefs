import Data.Vect 

(DecEq a, (y : a) -> DecEq (p y)) => DecEq (DPair a p) where
  decEq @{da} @{dp} (x ** y) (z ** w) with (decEq x z)
    decEq @{da} @{dp} (x ** y) (x ** w) | Yes Refl with (decEq @{dp x} y w)
      decEq (x ** y) (x ** y) | Yes Refl | Yes Refl = Yes Refl
      decEq (x ** y) (x ** w) | Yes Refl | No neq = No (\Refl => neq Refl)
    | No neq = No (\q => neq (cong {f = DPair.fst} q))

{-
import TParsec
import TParsec.Running
import Data.NEList

import Control.Isomorphism

except : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         Tok p -> All (Parser mn p (Tok p))
except t = guard (\t' => (t /= t')) anyTok

notChar : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
          Char -> All (Parser mn p (Tok p))
notChar = except . into

comments : (Alternative mn, Monad mn, Subset Char (Tok p), Inspect (Toks p) (Tok p), Eq (Tok p)) =>
           All (Parser mn p ())
comments = between (char ';') (char '>') (cmap () $ nelist $ notChar '>')

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok Char)

cmts : All (Parser' ())
cmts = (cmap () $ string ";>") `alt` comments

nelList : Iso (List a) (Maybe (NEList a))
nelList = MkIso fromList (maybe Nil NEList.toList) fromTo toFrom
  where 
  fromTo : (y : Maybe (NEList a)) -> fromList (maybe [] NEList.toList y) = y
  fromTo Nothing = Refl
  fromTo (Just (MkNEList h t)) = Refl

  toFrom : (x : List a) -> maybe [] NEList.toList (fromList x) = x
  toFrom [] = Refl
  toFrom (x::xs) = Refl
  -}