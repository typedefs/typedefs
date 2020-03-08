module Typedefs.Backend.Utils

import Typedefs.Backend.Data
import Typedefs.Typedefs
import Typedefs.Backend.Specialisation
import Typedefs.Names
import Typedefs.Either

import Control.Monad.State
import Data.Vect
import Data.SortedMap

%default total
%access public export

||| A variable environment. Left=free, Right=bound.
Env : Nat -> Type
Env k = Vect k (Either String Decl)

||| Generate a fresh environment, using the supplied string as a prefix for variable names.
freshEnv : String -> Env n
freshEnv var = map (\ix => Left (var ++ show (finToInteger ix))) range

||| Get the free names from the environment.
getFreeVars : (e : Env n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e)
  | (p ** v) = map (either id (const "")) v

-- TODO implementation in base was erroneous, this has been merged but is not in a version yet.
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

||| Produce a name for an anonymous `TMu` by simply concatenating its constructors.
export
nameMu : Vect n (Name, TDef' k a) -> Name
nameMu = concatMap (uppercase . fst)

||| "Flatten" all `TVar` references to `TMu`s into `TName`s named after the corresponding `TMu`, referencing `T0`s.
||| This is strictly meant to remove any `TVar`s from an AST.
||| The variable in the argument `TDef 1` is expected to reference the supplied name.
flattenMus : Name -> TDef' 1 b -> TDef' 0 b
flattenMus muName = flattenMu [muName]
  where
  -- DO NOT simply lift this function out to the top-level.
  -- Its behavior is dependent on the type of `makeDefs'`.
  -- (Specifically: all TVars must refer to a TMu, not to any free variables.)
  flattenMu : Vect (S n) Name -> TDef' (S n) a -> TDef' n a
  flattenMu names (TVar v)    = wrap $ TName (index v names) T0
  flattenMu _     T0          = T0
  flattenMu _     T1          = T1
  flattenMu names (TSum ts)   = assert_total $ TSum $ map (flattenMu names) ts
  flattenMu names (TProd ts)  = assert_total $ TProd $ map (flattenMu names) ts
  flattenMu names (TMu cs)    = assert_total $ TMu $ map (map (flattenMu ((nameMu cs) :: names))) cs
  flattenMu names (TApp f xs) = assert_total $ TApp f (map (flattenMu names) xs)
  flattenMu names (RRef i) {a = False} = wrap $ TName (index i names) T0
  flattenMu names (FRef i) {a = True } = FRef i
