module Typedefs.DependentLookup

import public Data.Vect
import public Decidable.Equality
import public Data.Vect.Elem

%default total

||| Lookup for maps with a shared index
public export
depLookup : DecEq t => {w : t} -> {0 f, g : t -> Type} -> DecEq (f w) =>
             (vs : Vect n (v : t ** (f v, g v))) -> f w ->
             Maybe (a : f w ** b : g w ** Elem (w ** (a, b)) vs)
depLookup [] item = Nothing -- Not found
depLookup ((n ** (key, val)) :: xs) item {w} with (decEq w n)
  -- if indices don't match then values can't possibly match since they have different type
  depLookup ((n ** (key, val)) :: xs) item {w = w} | (No contra) =
    do (a ** b ** prf) <- depLookup xs item
       pure (a ** b ** There prf)
  depLookup ((n ** (key, val)) :: xs) item {w = n} | (Yes Refl) with (decEq key item)
    depLookup ((n ** (item, val)) :: xs) item {w = n} | (Yes Refl) | (Yes Refl) =
      -- Index and Value match, return
      Just (item ** val ** Here {x=(n ** (item, val))})
    depLookup ((n ** (key, val)) :: xs) item {w = n} | (Yes Refl) | (No contra) =
      -- Index match but values differ
      do (a ** b ** prf) <- depLookup xs item
         pure (a ** b ** There prf)

public export
depLookupNil : DecEq t => {w : t} -> {f, g : t -> Type} -> {fkey : f w} ->
               DecEq (f w) =>
               depLookup {g} [] fkey = Nothing
depLookupNil = Refl
