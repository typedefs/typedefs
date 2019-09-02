module Typedefs.Backend.Specialisation

import Typedefs.Typedefs
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Typedefs.Names

import Effects

%default total

%access export

public export
interface Specialisation t where
  specialisedTypes : SortedMap String t

sumVect : Vect n (k ** Vect k a) -> (j ** Vect j a)
sumVect [] = (Z ** [])
sumVect ((k ** ks) :: xs) with (sumVect xs)
  | (j ** js) = (k + j ** ks ++ js)

||| extract all the references from a TDef
allRefs : (TDef n) -> (m ** Vect m Name)
allRefs T0          = (Z ** [])
allRefs T1          = (Z ** [])
allRefs (TSum xs)   = sumVect $ map (assert_total allRefs) xs
allRefs (TProd xs)  = sumVect $ map (assert_total allRefs) xs
allRefs (TVar i)    = (Z ** [])
allRefs (TMu xs)    = sumVect $ map (assert_total allRefs) $ map snd xs
allRefs (TApp x xs) = sumVect $ map (assert_total allRefs) xs
allRefs (FRef x)    = (1 ** [x])

noDupRefs : (tdef : TDef n) -> (m ** Vect m Name)
noDupRefs tdef = let (_ ** vs) = allRefs tdef in nub vs

nubLTE : Eq a => Vect n a -> (m ** (Vect m a, m `LTE` n))
nubLTE = nubBy' [] (==)
  where
    nubBy' : Vect m elem -> (elem -> elem -> Bool) -> Vect len elem -> (p ** (Vect p elem, p `LTE` len))
    nubBy' acc p []      = (_ ** ([], LTEZero))
    nubBy' acc p (x::xs) with (elemBy p x acc)
      | True  = let (n ** (vec, prf)) = nubBy' acc p  xs in (n ** (vec, lteSuccRight prf))
      | False with (nubBy' (x::acc) p xs)
        | (_ ** (tail, prf)) = (_ ** (x::tail, (LTESucc prf)))


||| extract all variables from a TDef
||| /!\ TDefR n will count resolved references as variables /!\
allVars : (tdef : TDef' n a) -> (m ** Vect m (Fin n))
allVars tdef = let ls = getUsedIndices tdef in (length ls ** fromList ls)

noDuplicateVars : TDef n -> (m ** Vect m (Fin n))
noDuplicateVars tdef = let (_ ** vs) = allVars tdef in nub vs

countVars : TDef n -> Nat
countVars tdef = fst $ noDuplicateVars tdef

weakenSN : (m : Nat) -> Fin (S n) -> Fin (S (n + m))
weakenSN m FZ = FZ
weakenSN m (FS x) = weaken $ weakenN m x

pairLookup : k -> SortedMap k v -> Either k (k, v)
pairLookup k m = MkPair k <$> maybeToEither k (lookup k m)

||| Build a vector of all the references, without duplication, present in the SortedMap
buildVect : (t : TDef n) -> SortedMap String b -> Either String (l ** Vect l (String, b))
buildVect tdef m = let (l ** refs) = noDupRefs tdef
                    in MkDPair l <$> traverse (flip pairLookup m) refs

traverseRefs : Applicative f => (String -> f (Fin k)) -> n `LTE` k -> TDef n -> f (TDef' k False)
traverseRefs fn prf         T0                   = pure T0
traverseRefs fn prf         T1                   = pure T1
traverseRefs fn prf         (TSum xs)            = TSum <$> traverse (assert_total $ traverseRefs fn prf) xs
traverseRefs fn prf         (TProd xs)           = TProd <$> traverse (assert_total $ traverseRefs fn prf) xs
traverseRefs _  LTEZero     (TVar _) {k = Z    } impossible
traverseRefs _  (LTESucc _) (TVar _) {k = Z    } impossible
traverseRefs fn prf         (TVar i) {k = (S k)} = pure $ TVar (weakenLTE i prf)
traverseRefs fn prf         (TApp x xs)          = assert_total $ traverseRefs fn prf (def x `ap` xs)
traverseRefs fn prf         (FRef x) {k = Z    } = absurd <$> fn x
traverseRefs fn prf         (FRef x) {k = (S k)} = RRef <$> fn x
traverseRefs fn prf         (TMu xs) {n}         = TMu <$>
  traverse (\(n, tdef) => MkPair n <$> (assert_total $ traverseRefs (map FS . fn) (LTESucc prf) tdef)) xs
  -- ^ this is a nightmare lambda but I couldn't lift it


elemIndexVal : Eq a => a -> Vect m a -> Either a (Fin m)
elemIndexVal x xs = maybeToEither x $ elemIndex x xs

||| This is where the magic happens, replaces all free variables by bounded ones using the index in the vector
replaceRefs : (TDef n) -> Vect k String -> Either String (TDef' (n + k) False)
replaceRefs tdef vs {n} = traverseRefs (map (shift n) . flip elemIndexVal vs) (lteAddRight n) tdef

||| Extends a TDef n with its context into a TDef (n + k) along with its new context after resolving references
extendContext : TDef n -> SortedMap String b -> Vect n b ->
                Either String (k ** (TDefR (n + k), Vect (n + k) b))
extendContext def m c = do (r ** refs) <- buildVect def m
                           replaced <- replaceRefs def (map fst refs)
                           pure (r ** (replaced, c ++ (map snd refs)))



