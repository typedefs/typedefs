module Backend.Utils

import Typedefs
import Types

import Control.Monad.State
import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export

||| A parametric type declaration (no definition, only name and parameters).
record Decl where
  constructor MkDecl

  ||| The name of the type.
  name   : Name

  ||| The names of the type's parameters.
  params : Vect n Name -- TODO is number of parameters enough?

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

||| Get a list of the de Brujin indices that are actually used in a `TDef`.
getUsedIndices : TDef n -> List (Fin n)
getUsedIndices T0         = []
getUsedIndices T1         = []
getUsedIndices (TSum xs)  = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TProd xs) = assert_total $ nub $ concatMap getUsedIndices xs
getUsedIndices (TVar i)   = [i]
getUsedIndices (TMu xs)   = assert_total $ nub $ concatMap ((concatMap weedOutZero) . getUsedIndices . snd) xs
  where weedOutZero : Fin (S n) -> List (Fin n)
        weedOutZero FZ     = []
        weedOutZero (FS i) = [i]
getUsedIndices (TApp f xs) = let fUses = assert_total $ getUsedIndices (def f)
                              in nub $ concatMap (assert_total getUsedIndices) $ map (flip index xs) fUses

||| Filter out the entries in an `Env` that is referred to by a `TDef`.
getUsedVars : Env n -> (td: TDef n) -> Env (length (getUsedIndices td))
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Only perform an action if a name is not already present in the state. If the action is performed, the name will be added.
ifNotPresent : Eq name => name -> State (List name) (List def) -> State (List name) (List def)
ifNotPresent n gen = do
  st <- get
  if n `List.elem` st
    then pure []
    else modify {stateType=List name} (n ::) *> gen 

-- TODO implementation in base was erroneous, this has been merged but is not in a version yet. 
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

||| Print a document with a width of 80 symbols.
print : Doc -> String
print = toString 1 80

||| Vertically concatenate a list of documents with two newlines (i.e. one empty line) as separator.
vsep2 : List Doc -> Doc
vsep2 = vsep . punctuate line

||| Produce a name for an anonymous `TMu` by simply concatenating its constructors.
nameMu : Vect n (Name, TDef k) -> Name
nameMu = concatMap (uppercase . fst)

||| "Flatten" all `TVar` references to `TMu`s into `TName`s named after the corresponding `TMu`, referencing `T0`s.
||| This is strictly meant to remove any `TVar`s from an AST.
||| The variable in the argument `TDef 1` is expected to reference the supplied name.
flattenMus : Name -> TDef 1 -> TDef 0
flattenMus muName = flattenMu [muName]
  where
  mutual
   -- DO NOT simply lift this function out to the top-level.
   -- Its behavior is dependent on the type of `makeDefs'`.
   -- (Specifically: all TVars must refer to a TMu, not to any free variables.)
   flattenMu : Vect (S n) Name -> TDef (S n) -> TDef n
   flattenMu names (TVar v)    = wrap $ TName (index v names) T0
   flattenMu _     T0          = T0
   flattenMu _     T1          = T1
   flattenMu names (TSum ts)   = assert_total $ TSum $ map (flattenMu names) ts
   flattenMu names (TProd ts)  = assert_total $ TProd $ map (flattenMu names) ts
   flattenMu names td@(TMu cs) = def $ flattenMu' names $ TName (nameMu cs) td
   flattenMu names (TApp f xs) = assert_total $ TApp f (map (flattenMu names) xs)

   flattenMu' : Vect (S n) Name -> TNamed (S n) -> TNamed n
   flattenMu' names (TName name body) = case body of
     TMu cases => assert_total $ TName name $ TMu $ map (map (flattenMu (name :: names))) cases
     _         => assert_total $ TName name $ flattenMu names body 