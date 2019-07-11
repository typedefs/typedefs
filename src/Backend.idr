module Backend

import Data.Vect
import Data.NEList

import Names
import Typedefs
import Backend.Utils

import Data.Vect
import Text.PrettyPrint.WL

%default total
%access public export

data ZeroOrUnbounded : (Nat -> Type) -> Bool -> Type where
  Unbounded : p n -> ZeroOrUnbounded p True
  Zero : p Z -> ZeroOrUnbounded p False

fromSigma : {p : Nat -> Type} -> (b : Bool) -> (n ** p n) -> Maybe (ZeroOrUnbounded p b)
fromSigma True  (n  **pn) = Just $ Unbounded $ pn
fromSigma False (Z  **pz) = Just $ Zero $ pz
fromSigma False (S _** _) = Nothing

||| Interface for interpreting type definitions as ASTs.
||| @def      the type representing definitions.
||| @type     the type representing types.
||| @freeVars flag contolling if type definition can have free variables.
interface ASTGen def type (freeVars : Bool) | def where
  ||| Given a list of `TNamed`, generate their corresponding type signatures.
  msgType        : ZeroOrUnbounded TNamed freeVars -> type

  ||| Generate definitions for a list of `TNamed`.
  generateTyDefs : NEList (ZeroOrUnbounded TNamed freeVars) -> List def

  ||| Generate serialisation and deserialisation term definitions for a
  ||| a `TNamed` and all its helper definitions.
  generateTermDefs : ZeroOrUnbounded TNamed freeVars -> List def

||| Interface for code generators that can generate code for type definitions and
||| type signatures independently of each other, for example Haskell and ReasonML.
||| @def  the type representing definitions.
||| @type the type representing types.
interface CodegenIndep def type | def where
  ||| Generate source code for a type signature.
  typeSource : type -> Doc

  ||| Generate source code for a type definition.
  defSource  : def -> Doc

  ||| A common preamble that code generated by `typeSource` and
  ||| `defSource` may use.
  preamble : Doc

||| Use the given backend to generate code for a list of type definitions.
generateDefs : (def : Type) -> (ASTGen def type fv, CodegenIndep def type) => NEList (n ** TNamed n) -> Maybe Doc
generateDefs {fv} def tns = 
  (\nel => 
    vsep2 $ (preamble {def}) ::
    (  map defSource (generateTyDefs {def} nel 
    ++ concatMap (generateTermDefs {def}) nel)
    )
  ) <$> (traverse (fromSigma fv) tns)

||| Use the given backend to generate code for a list of type signatures.
generateType : (def : Type) -> (ASTGen def type fv, CodegenIndep def type) => NEList (n ** TNamed n) -> Maybe Doc
generateType {fv} def tns = 
  (concatMap (typeSource {def} . msgType {def})) <$> (traverse (fromSigma fv) tns)
  --typeSource {def} (msgType {def} tns)

||| Interface for code generators that need to generate code for type definitions and
||| type signatures at the same time, for example the JSON schema backend.
||| @def  the type representing type definitions.
||| @type the type representing type signatures.
interface CodegenInterdep def type where
  ||| Generate source code for a type signature and a list of helper definitions.
  sourceCode   : type -> List def -> Doc

{-
||| Use the given backend to generate code for a list of type definitions.
generate : (def : Type) -> (ASTGen def type fv, CodegenInterdep def type) => NEList (n ** TNamed n) -> Maybe Doc
generate {fv} def tns = 
  (\nel => 
    
    let 
      tt0 = (msgType {def}) <$> nel
      tt = (generateTyDefs {def} nel) ++ (concatMap (generateTermDefs {def}) nel)
      
    in ?wat
  ) <$> (traverse (fromSigma fv) tns)
  
  --sourceCode (msgType {def} tns) (generateTyDefs {def} tns ++ generateTermDefs {def} tns)

record SpecialiseEntry where
  constructor MkSpecialiseEntry
  tdef : TDef 0
  ||| name of type used for specialisation
  targetType : String
  ||| name of function of target type generateType tdef -> targetType
  encodeFun : String
  ||| name of function of target type targetType -> generateType tdef
  decodeFun : String

||| Generate type definitions according to an *ordered* set of specialisation entries.
generateDefsSpecialised : Backend lang => Vect (S m') SpecialiseEntry -> (n : Nat) -> TDef n -> List lang
generateDefsSpecialised {lang} {m' = m'} table n td = generateTyDefs e td'
   where m : Nat
         m = S m'
         e : Env (n + m)
         e = freshEnv {lang} n ++ map (\ s => Right $ MkDecl (targetType s) []) table
         traverseTD : (n : Nat) -> (Fin m, SpecialiseEntry) -> TDef (n + m) -> TDef (n + m)
         traverseTD n (i, se) t = if t == weakenTDef (tdef se) _ (lteAddRight 0)
                                    then replace prf (TVar (fromNat (n + toNat i)))
                                    else go t
             where prf : m + n = n + m
                   prf = plusCommutative m n
                   go : TDef (n + m) -> TDef (n + m)
                   go T0 = T0
                   go T1 = T1
                   go (TSum xs)  = TSum (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TProd xs) = TProd (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TMu xs)   = TMu (assert_total $ map (\(c, t) => (c,traverseTD (S n) (i, se) t)) xs)
                   --go (TName name t) = TName name (traverseTD n (i, se) t)
                   go (TApp f xs) = ?goTApp
                   go x = x -- only TVar i case left
         td' : TDef (n + m)
         td' = foldl (flip (traverseTD n)) (weakenTDef td (n + m) (lteAddRight n)) (zip range table)
-}
