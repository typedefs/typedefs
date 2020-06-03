module Typedefs.TermWrite

import Typedefs.Idris
import Typedefs.DependentLookup
import Typedefs.TypedefsDecEq
import Typedefs.Names

import Data.Vect

import Data.Bytes
import Data.ByteArray

import Language.JSON

%default total

-- serialization


||| A proof that each Type in the indexed list can be converted into the target type
public export
data HasGenericWriters : (target : Type) -> (types : Vect n Type) -> Type where
  Nil  : HasGenericWriters a Nil
  (::) : (src -> trg) -> HasGenericWriters trg xs -> HasGenericWriters trg (src :: xs)

namespace SpecialisedWriters
  ||| Prove that there exist a writer function for every type in the specialisation list
  public export
  data HasSpecialisedWriter : (target : Type) -> (specialised : SpecialList l) -> Type where
    Nil  : HasSpecialisedWriter a []
    (::) : {n : Nat} -> {def : TDefR n} -> {constr : TypeConstructor n} ->
           ({args : Vect n Type} -> HasGenericWriters a args -> ApplyVect constr args -> a) ->
           HasSpecialisedWriter a xs ->
           HasSpecialisedWriter a ((n ** (def, constr)) :: xs)

||| Lookup in the specialised context for the function that converts a special type to its target representation
lookupTypeReplacement : {sp : SpecialList l} -> (e : Elem (n ** (td, constr)) sp) ->
                        {target : Type} ->
                        (sw : HasSpecialisedWriter target sp) ->
                        {args : Vect n Type} -> HasGenericWriters target args ->
                        ApplyVect constr args -> target
lookupTypeReplacement Here (s :: sp) = s
lookupTypeReplacement (There e) (s :: sp) = lookupTypeReplacement e sp

||| Returns the index and the type of a sum from an array of TDefs
injectionInv : (ts : Vect (2 + k) (TDefR n)) -> Tnary' sp tvars ts Either -> (i : Fin (2 + k) ** Ty' sp tvars (index i ts))
injectionInv [a,b] (Left x) = (0 ** x)
injectionInv [a,b] (Right y) = (1 ** y)
injectionInv (a::b::c::tds) (Left x) = (0 ** x)
injectionInv (a::b::c::tds) (Right y) =
  let (i' ** y') = injectionInv (b::c::tds) y in (FS i' ** y')

getVariable : {ts : Vect (S n) Type} -> (i : Fin (S n)) -> (ws : HasGenericWriters target ts) -> index i ts -> target
getVariable FZ (f :: z) x {ts = (y :: xs)} = f x
getVariable (FS FZ) (_ :: f :: ws) x = f x
getVariable (FS (FS y)) (w :: ws) x = getVariable (FS y) ws x

||| Given a vector of TDef n and n types to fill its holes, return the vector of types correpondng to those tdefs
FromTDefToTy : {n : Nat} -> SpecialList l -> Vect n Type -> Vect k (TDefR n) -> Vect k Type
FromTDefToTy sp types vs = map (Ty' sp types) vs

||| Magically generate the writers for a vector of TDefs in argument position
|||
||| For some reason this couldn't be placed in a where-clause inside `serialise`. The lookup for
||| instances of `TDefSeraliser` would get confused and say that there aren't any suitable instances
||| for `serialiser`. That's why we simply pass it as a partially applied function
makeWriters : {target : Type} -> {sp : SpecialList l} ->
               (tys : Vect n Type) ->
               (spp : HasSpecialisedWriter target sp) ->
               (gen : HasGenericWriters target tys) ->
               ((tdef : TDefR n) -> Ty' sp tys tdef -> target) ->
               (vs : Vect k (TDefR n)) ->
               HasGenericWriters target (FromTDefToTy sp tys vs)
makeWriters tys spp gen fn [] = []
makeWriters tys spp gen fn (td :: tds) = (fn td) :: (makeWriters tys spp gen fn tds)

public export
interface TDefSerialiser target where
  unitVal : target

  ||| How to convert a sum into a term in the target type
  foldSum : {ts : Vect n Type} -> {sp : SpecialList l} ->
            HasSpecialisedWriter target sp ->
            HasGenericWriters target ts ->
            (args : Vect (2 + k) (TDefR n)) ->
            Ty' sp ts (TSum args) -> target

  ||| How to convert a prod into a term in the target type
  foldProd : {ts : Vect n Type} -> {sp : SpecialList l} ->
             HasSpecialisedWriter target sp ->
             HasGenericWriters target ts ->
             (args : Vect (2 + k) (TDefR n)) ->
             Ty' sp ts (TProd args) -> target

  ||| How to decorate a mu term
  muPrefix : target -> target

  ||| Convert an arbitrary TDef into a term in the target format
  |||
  ||| Given an arbitrary specialisation list, a proof that every specialised type has a writer
  ||| and a proof that every type that will inhabit each type variable also has a writer, return
  ||| a function that will take a Typedef and its Idris term and convert it into a term in the
  ||| target format
  ||| @n : The number of free variables in the Typedefs
  ||| @ts : The vector of types that will inhabit the free variables
  ||| @sp : The specialisation list of types that will be replaced by a specialised version
  ||| @spp : A proof that every specialised constructor and its arguments have a writer
  ||| @ws : A proof that every type parameter has a writer
  serialise : {n : Nat} -> {ts : Vect n Type} -> {sp : SpecialList l} ->
              (spp : HasSpecialisedWriter target sp) -> (ws : HasGenericWriters target ts) ->
              (td : TDefR n) -> Ty' sp ts td -> target
  serialise spp ws T1           x = unitVal
  serialise spp ws (TSum args)  x = foldSum spp ws args x
  serialise spp ws (TProd args) x = foldProd spp ws args x
  serialise spp ws (RRef i)     x = getVariable i ws x
  serialise spp ws (TVar i)     x = getVariable i ws x

  -- first lookup the specialisation context
  serialise spp {sp} {ts} {n} ws (TApp (TName _ def) ys) x with (depLookup sp def)
    serialise spp {sp} {ts} {n} ws (TApp (TName _ def) ys) x | Nothing =

      -- if there is nothing, proceed as is nothing changed
      -- if we had a proof that no substitutions we performed we could remove the `believe_me`
      assert_total $ serialise spp ws (def `ap` ys) (believe_me x)
    serialise spp {sp} {ts} {n} ws (TApp (TName _ def) ys) x | (Just (d ** constr ** prf)) =

      -- Otherwise, replace the type using the magic lookup.
      -- This requires to pass a list of writer functions for the type arguments. Since the
      -- type arguments come from the vector of TDefs passed in arguments to the TApp we
      -- generate a new `HasGenericWriter` using `serialise` itself a writer function from
      -- source type (each TDef in the argument vector) to the target type.
      lookupTypeReplacement prf spp (makeWriters ts spp ws (assert_total $ serialise spp ws) ys) x

  -- first lookup the specialisation context
  serialise spp {sp} ws (TMu td) x {ts} with (depLookup sp (TMu td))
    serialise spp ws (TMu td) (Inn x') {ts = ts} | Nothing =

      -- if we didn't find anything we proceed as usual
      -- if we had a proof that no substitutions we performed we could remove the `believe_me`
      -- before returning we wrap the result in the `muPrefix` decorator
      let inner = assert_total $ serialise spp {ts=(Mu ts (args td))::ts}
                                           ((serialise [] ws (TMu td)) :: ws)
                                           (args td)
                                           (believe_me x')
       in muPrefix inner
    serialise spp ws (TMu td) x {ts = ts} | (Just (def ** constr ** prf)) =

      -- Otherwise lookup the type to be replaced and apply it using the vector of types given
      -- in the context
      lookupTypeReplacement prf spp {args=ts} ws x

---------------------------------------------------------------------------------------------
-- Strings                                                                                 --
---------------------------------------------------------------------------------------------

public export
TDefSerialiser String where

  unitVal = "()"

  foldSum sp ws ([x,_]) (Left l) =
    parens $ "left "  ++ serialise sp ws x l
  foldSum sp ws ([_,y]) (Right r) =
    parens $ "right " ++ serialise sp ws y r
  foldSum sp ws ((x::_::_::_)) (Left l) =
    parens $ "left "  ++ serialise sp ws x l
  foldSum sp ws ((_::y::z::zs)) (Right r) =
    parens $ "right " ++ serialise sp ws (TSum (y::z::zs)) r

  foldProd sp ws ([x,y]) (a, b) =
    parens $ "both "  ++ serialise sp ws x a ++ " " ++ serialise sp ws y b
  foldProd sp ws ((x::y::z::zs)) (a, b) =
    parens $ "both "  ++ serialise sp ws x a ++ " " ++ serialise sp ws (TProd (y::z::zs)) b

  muPrefix inner = "(inn " ++ inner ++ ")"

---------------------------------------------------------------------------------------------
-- Binary                                                                                  --
---------------------------------------------------------------------------------------------

serializeInt : {n : Nat} -> (Fin n) -> Bytes
serializeInt x = pack [prim__truncBigInt_B8 (finToInteger x)]

public export
TDefSerialiser Bytes where

  unitVal = empty

  foldSum sp ws args tv =
     let (i ** x') = injectionInv args tv in
     (serializeInt i) ++ (assert_total $ serialise sp ws (index i args) x')

  foldProd sp ws [a, b] (x, y) =
    (serialise sp ws a x) ++ (serialise sp ws b y)
  foldProd sp ws (a::b::c::tds) (x, y) =
    (serialise sp ws a x) ++ (serialise sp ws (TProd (b::c::tds))) y

  muPrefix = id

---------------------------------------------------------------------------------------------
-- JSON                                                                                    --
---------------------------------------------------------------------------------------------


makeFields : Nat -> List String
makeFields n = map (("_" ++) . show) [0 .. n]

public export
TDefSerialiser JSON where

  unitVal = JObject []

  -- Products are serialised as { "_0" : a, "_1" : b, ... , "_x" : n } where the key stands for the
  -- index in the product
  foldProd sp ws args tv =  let res = serialiseTNaryProd sp ws args tv in
                            JObject (zip (makeFields (length args)) res)
    where
      serialiseTNaryProd : {sp : SpecialList l} ->
                           HasSpecialisedWriter JSON sp -> HasGenericWriters JSON ts ->
                           (defs: Vect (2 + k) (TDefR n)) ->
                           Tnary' sp ts defs Pair -> List JSON
      serialiseTNaryProd sp writers [x, y] (a, b) =
        [serialise sp writers x a, serialise sp writers y b]
      serialiseTNaryProd sp writers (x :: y :: z :: zs) (a , b) =
        serialise sp writers x a :: serialiseTNaryProd sp writers (y :: z :: zs) b

  -- Mus are identified by an obect with a single `inn` field
  muPrefix inner =  JObject [("inn",  inner)]

  -- Sums are serialized as { "_x" : term } where x is the index in the sum
  foldSum sp ws args tv =
    let (i ** def) = injectionInv args tv in
        JObject [("_"++ show (toNat i), assert_total $ serialise sp ws (index i args) def)]

