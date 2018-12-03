module Backend.Haskell

import Data.HVect
import Data.Vect
import Control.Monad.State
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

%default partial
%access public export

{-
TODO
 Remove TDef -> String funs
 Rename funs
 Move and rename SynEnv
-}


data HaskellType : Type where
  T0     :                                     HaskellType
  T1     :                                     HaskellType
  TProd  :         Vect (2 + k) HaskellType -> HaskellType
  TVar   :         Name                     -> HaskellType
  TParam : Name -> HaskellType              -> HaskellType

isSimple : HaskellType -> Bool
isSimple (TParam _ t) = case t of
                          T1 => True
                          _   => False
isSimple _            = True

data HaskellDef : Type where
  Synonym : (name : Name) -> (vars : Vect n Name) -> HaskellType -> HaskellDef
  ADT     : (name : Name) -> (vars : Vect n Name) -> Vect k (Name, HaskellType) -> HaskellDef

mutual
  makeDoc : HaskellType -> Doc
  makeDoc T0              = text "Void"
  makeDoc T1              = text "()"
  makeDoc (TProd xs)      = tupled . toList $ map makeDoc xs
  makeDoc (TVar v)        = text (lowercase v)
  makeDoc (TParam name t) = docifyCase (name,t) -- text (uppercase name) |+| hsep (toList (empty::map guardParen ts))
    where
    guardParen : HaskellType -> Doc
    guardParen ht = if isSimple ht then makeDoc ht else parens (makeDoc ht)
  
  docifyCase : (Name, HaskellType) -> Doc
  docifyCase (n, T1) = text (uppercase n)
  docifyCase (n, TProd ts) = text (uppercase n) |++| hsep (toList (map (\t => if isSimple t then makeDoc t else parens (makeDoc t)) ts))
  docifyCase (n, ht) = text (uppercase n) |++| makeDoc ht

docify : HaskellDef -> Doc
docify (Synonym name vars body) = text "type" |++| text (uppercase name) |+| hsep (empty :: toList (map (text . lowercase) vars)) |++| equals |++| makeDoc body
docify (ADT name vars cases) = text "data" |++| text (uppercase name) |+| hsep (empty :: toList (map (text . lowercase) vars)) |++| equals |++| hsep (punctuate (text " |") (toList $ map docifyCase cases))

--guardPar : String -> String
--guardPar str = if any isSpace $ unpack str then parens str else str

--nameWithParams : Name -> Env n -> String
--nameWithParams name e = withSep " " id (uppercase name::map lowercase (getFreeVars e))

SynEnv : Nat -> Type
SynEnv n = Vect n (Either Name (Name, HaskellType))

freshSynEnv : (n: Nat) -> SynEnv n
freshSynEnv n = unindex {n} (\f => Left ("x" ++ show (finToInteger f)))

getFreeVars : (e : SynEnv n) -> Vect (fst (Vect.filter Either.isLeft e)) String
getFreeVars e with (filter isLeft e) 
  | (p ** v) = map (either id (const "")) v

foldr1' : (a -> a -> a) -> Vect (S n) a -> a
foldr1' f [x]      = x
foldr1' f (x::y::xs)   = f x (foldr1' f (y::xs))

makeParamType : Vect n Name -> HaskellType
makeParamType []            = T1
makeParamType [p]           = TVar p
makeParamType ps@(p::q::qs) = TProd (map TVar ps)

makeSynType : SynEnv n -> TDef n -> HaskellType
makeSynType     _ T0             = T0
makeSynType     _ T1             = T1
makeSynType     e (TSum xs)      = foldr1' (\t1,t2 => TParam "Either" (TProd [t1, t2])) (map (makeSynType e) xs) -- why does this require custom foldr1?
makeSynType     e (TProd xs)     = TProd $ map (makeSynType e) xs
makeSynType     e (TVar v)       = either TVar (uncurry TParam) $ Vect.index v e
makeSynType     e (TMu name _)   = TParam name (makeParamType $ getFreeVars e)
makeSynType     e (TName name _) = TParam name (makeParamType $ getFreeVars e)


-- makeType : Env n -> TDef n -> Doc
-- makeType     _ T0             = text "Void"
-- makeType     _ T1             = text "()"
-- makeType {n} e (TSum xs)      = tsum xs
--   where
--   tsum : Vect (2 + _) (TDef n) -> Doc
--   tsum [x, y]              = text "Either" |++| parens (makeType e x) |++| parens (makeType e y)
--   tsum (x :: y :: z :: zs) = text "Either" |++| parens (makeType e x) |++| parens (tsum (y :: z :: zs))
-- makeType     e (TProd xs)     = tupled . toList $ map (makeType e) xs
-- makeType     e (TVar v)       = text $ either id id $ Vect.index v e
-- makeType     e (TMu name _)   = text $ nameWithParams name e
-- makeType     e (TName name _) = text $ nameWithParams name e

makeDefs : SynEnv n -> TDef n -> State (List Name) (List HaskellDef)
makeDefs _ T0            = pure []
makeDefs _ T1            = pure []
makeDefs e (TProd xs)    = map concat $ traverse (makeDefs e) (toList xs)
makeDefs e (TSum xs)     = map concat $ traverse (makeDefs e) (toList xs)
makeDefs _ (TVar v)      = pure []
makeDefs e (TMu name cs) = 
   do st <- get 
      if List.elem name st then pure [] 
       else let
          newEnv = Right (name, makeParamType $ getFreeVars e) :: e
          args = map (map (makeSynType newEnv)) cs
         in
        do res <- map concat $ traverse {b=List HaskellDef} (\(_, bdy) => makeDefs newEnv bdy) (toList cs) 
           put (name :: st)
           pure $ ADT name (getFreeVars e) args :: res -- (text "data" |++| text dataName |++| equals |++| args) :: res
--  where
--  mkArg : Env (S n) -> (Name, TDef (S n)) -> (Name, HaskellType)
--  mkArg _ (cname, T1)       = (cname, T1)
--  mkArg e (cname, TProd xs) = text cname |++| (hsep . toList) (map (makeType e) xs)
--  mkArg e (cname, ctype)    = text cname |++| makeType e ctype
makeDefs e (TName name body) = 
  do st <- get 
     if List.elem name st then pure []
       else 
        do res <- makeDefs e body 
           put (name :: st)
           pure $ Synonym name (getFreeVars e) (makeSynType e body) :: res -- (text "type" |++| text (nameWithParams name e) |++| equals |++| makeType e body) :: res

-- generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
-- generateType : TDef n -> Doc
-- generateType {n} = makeType (freshEnv n)

-- generate data definitions
generate : TDef n -> Doc
generate {n} td = vsep2 . map docify . reverse $ evalState (makeDefs (freshSynEnv n) td) []