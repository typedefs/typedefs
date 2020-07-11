module Typedefs.Backend.Swift.TermGen

import Typedefs.Backend.Swift.Data
import Typedefs.Backend.Data
import Data.Vect
import Typedefs.Names
import Typedefs.Typedefs

enumerate : (n : Nat) -> Vect n Nat
enumerate Z = []
enumerate (S n) = Z :: map S (enumerate n)

mkTypeName : String -> (n : Nat) -> String
mkTypeName x n = x ++ show n

typeNames : (n : Nat) -> String -> Vect n String
typeNames n prefix = map (mkTypeName prefix) (enumerate n)

sumCase : Nat -> (String, List SwType)
sumCase n = (mkTypeName "s" n, pure $ SwTVar (mkTypeName "X" n))

sumName : Nat -> String
sumName = mkTypeName "Sum"

||| Creates an enumeration with n cases from 0 to `n` with type variables X0 ... XN
||| this is used because Swift does not support overlapping protocol implementations
||| So instead we create this definition with serialiser and deserialiser and all
||| anonymous sums are typealiases for this type
createSumDecl : Nat -> SwDecl
createSumDecl cases = SwDeclType $
    Enum Normal
         (MkDecl (sumName cases) (typeNames cases "X"))
         (toList $ map sumCase $ enumerate cases)

||| Top level generator for TDefs
compileTDef : TDefR n -> List SwDecl
compileTDef T0 = []
compileTDef T1 = []
compileTDef (TSum xs) = ?compileTDef_rhs_3
compileTDef (TProd xs) = ?compileTDef_rhs_4
compileTDef (TVar i) = ?compileTDef_rhs_5
compileTDef (TMu xs) = ?compileTDef_rhs_6
compileTDef (TApp x xs) = ?compileTDef_rhs_7
compileTDef (RRef x) = ?compileTDef_rhs_8






