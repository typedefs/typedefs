||| This module is by itself because its only function takes ages to compile
module DependentLookup

import Decidable.Equality
import Data.Vect

%default total

||| Lookup for maps with a shared index
public export
depLookup : DecEq t => {w : t} -> {f, g : t -> Type} -> DecEq (f w) =>
            (vs : Vect n (v : t ** (f v, g v))) ->
            f w ->
            Maybe (a : f w ** b : g w ** Elem (w ** (a, b)) vs)
depLookup [] item = Nothing -- Not found
depLookup ((MkDPair i (key, val)) :: xs) item {w} with (decEq w i)
  -- if indices don't match then values can't possibly match since they have different type
  depLookup ((MkDPair i (key, val)) :: xs) item {w = w} | (No contra) =
    do (a ** b ** prf) <- depLookup xs item
       pure (a ** b ** There prf)
  depLookup ((MkDPair i (key, val)) :: xs) item {w = i} | (Yes Refl) with (decEq key item)
    depLookup ((MkDPair i (item, val)) :: xs) item {w = i} | (Yes Refl) | (Yes Refl) =
      -- Index and Value match, return
      Just (item ** val ** Here {x=(i ** (item, val))})
    depLookup ((MkDPair i (key, val)) :: xs) item {w = i} | (Yes Refl) | (No contra) =
      -- Index match but values differ
      do (a ** b ** prf) <- depLookup xs item
         pure (a ** b ** There prf)

