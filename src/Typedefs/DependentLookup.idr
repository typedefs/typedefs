||| Lookup on a map with the type of key and value depending on an another value
module DependentLookup

%default total


||| A heterogenous map with key and value with type `f v` and `g v` for a given `v : t`
public export
data HMap : Nat -> (f, g : t -> Type) -> Type where
  Nil : HMap Z f g
  (::) : {t : Type} -> (v : t ** (f v, g v)) -> HMap n f g -> HMap (S n) f g

||| A proof that an element belong to the map
public export
data HElem : (a ** (f a, g a))-> HMap n f g -> Type where
  Here : {f, g : t -> Type} -> HElem x (x :: xs)
  There : HElem x xs -> HElem x (y :: xs)

||| Lookup for dependent maps with a shared index
public export
depLookup : DecEq t => {w : t} -> {f, g : t -> Type} -> DecEq (f w)
           => (item : f w)
           -> (m : HMap n f g)
           -> Maybe (found : g w ** HElem (w ** (item, found)) m)
depLookup item [] = Nothing -- we're done looking, pack it up boys
depLookup item {w} ((v ** (key, val)) :: xs) with (decEq w v)
  depLookup item {w=v} ((v ** (key, val)) :: xs) | (Yes Refl) with (decEq key item)
    depLookup item {w=v} {f} {g} ((v ** (item, val)) :: xs) | (Yes Refl) | Yes Refl = 
      -- index and key match, we found it
      Just (val ** Here {f} {g})
    depLookup item {w=v} ((v ** (key, val)) :: xs) | (Yes Refl) | No ctr = 
      -- indicies match but keys don't match
      do (val ** prf) <- depLookup item xs
         Just (val ** There prf)
  depLookup item ((v ** (key, val)) :: xs) | (No contra) =
    -- indicies don't match, keep looking
    do (val ** prf) <- depLookup item xs
       Just (val ** There prf)
