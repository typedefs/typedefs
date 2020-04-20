module Typedefs.Test.IdrisReferences

import Data.Vect
import Typedefs.Typedefs
import Typedefs.Library

Var0 : TDefR 1
Var0 = RRef 0

||| Replacing reference
instanceLists : (GammaTy [(1 ** List)] Var0) Nat
instanceLists = [1,2,3]

||| Replacing regerence with 2-argument constructor
instanceEither : (GammaTy [(2 ** Either)] Var0) Nat String
instanceEither = Right "test"

||| Replacing 2-arguments variable with two 1-argument constructor
instancePair : (GammaTy [(1 ** List), (1 ** List)] TPair) String Nat
instancePair = (["this", "is", "a", "test"], [1,2,3])

||| instanciating 1-argument constructor with 1-argument constructor
instanceMaybe : (GammaTy [(1 ** List)] TMaybe) Nat
instanceMaybe = Inn (Right [3])

||| Instance 1-argument constructor with reference
instanceRef : (GammaTy [(2 ** Either)] (TMaybe `ap` [Var0])) Nat String
instanceRef = Inn (Right (Right "hello"))


