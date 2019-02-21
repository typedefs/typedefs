module Backend.Utils

import Typedefs
import Types

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export

-- TODO implementation in base was erroneous, this has been merged but is not in a version yet. 
foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]        = x
foldr1' f (x::y::xs) = f x (foldr1' f (y::xs))

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

||| Print a document with a width of 80 symbols.
print : Doc -> String
print = toString 1 80

||| Vertically concatenate a list of documents with two newlines (i.e. one empty line) as separator.
vsep2 : List Doc -> Doc
vsep2 = vsep . punctuate line

||| Produce a name for an anonymous `TMu` by simply concatenating its constructors.
nameMu : Vect n (Name, TDef k) -> Name
nameMu = concatMap fst

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