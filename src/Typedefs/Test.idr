module Typedefs.Test

import Typedefs.Typedefs
import Typedefs.Names
import Typedefs.Text
import Typedefs.Backend.Utils

import Data.Vect
import Data.NEList

import Specdris.Spec
import Text.PrettyPrint.WL

%default total
%access public export

bit : TNamed' 0 b
bit = TName "Bit" $ TSum [T1, T1]

byte : TNamed' 0 b
byte = TName "Byte" $ powN 8 bit

maybe : TNamed' 1 b
maybe = TName "Maybe" $  TSum [T1, TVar 0]

bar : TNamed' 2 b
bar = TName "Bar" $ TProd [TVar 1, TVar 0]

foo : TNamed' 3 b
foo = TName "Foo" $ TApp bar [TProd [TVar 1, TVar 2], TVar 0]

list : TNamed' 1 b
list = TName "List" $ TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

maybe2 : TNamed' 1 b
maybe2 = TName "Maybe2" $ TMu [("Nothing", T1), ("Just", TVar 1)]

nat : TNamed' 0 b
nat = TName "Nat" $ TMu [("Z", T1), ("S", TVar 0)]

listNat : TNamed' 0 b
listNat = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [weakenTDef (wrap nat) 1 LTEZero, TVar 0])]

parametricSynonym : TNamed' 1 b
parametricSynonym = alias "ParSyn" maybe

parametricSynonym2 : TNamed' 1 b
parametricSynonym2 = alias "ParSyn2" maybe2

aplusbpluscplusd : TNamed' 4 b
aplusbpluscplusd = TName "aplusbpluscplusd" $ TSum [TVar 0, TVar 1, TVar 2, TVar 3]

oneoneoneone : TNamed' 0 b
oneoneoneone = TName "oneoneoneone" $ TSum [T1, T1, T1, T1]

listByte : TNamed' 0 b
listByte = TName  "ListByte" $ TMu [("NilC", T1), ("ConsC", TProd [weakenTDef (wrap byte) 1 LTEZero, TVar 0])]

tripleByteListnatAlpha : TNamed' 1 b
tripleByteListnatAlpha = TName "Triple" (TProd [weakenTDef (wrap byte) 1 LTEZero, weakenTDef (wrap listNat) 1 LTEZero, TVar 0])

unusedFreeVars : TNamed' 42 b
unusedFreeVars = TName "Id" (TVar 0)

voidOrUnit : TNamed' 0 b
voidOrUnit = TName "VoidOrUnit" $ TSum [T0, T1]

nonlinear : TNamed' 1 b
nonlinear = TName "Nonlinear" $ TProd [TVar 0, TVar 0]

listAlphaOrBeta : TNamed' 2 b
listAlphaOrBeta = TName "listAlphaOrBeta" $ TApp list [TSum [TVar 0, TVar 1]]

listBitOrByte : TNamed' 0 b
listBitOrByte = TName "listBitOrByte" $ TApp listAlphaOrBeta [wrap bit, wrap byte]

nestedMu1 : TNamed' 2 b
nestedMu1 = TName "nestedMu1" $ TMu [("Foobar", shiftVars (def listAlphaOrBeta))]

nestedMu2 : TNamed' 1 b
nestedMu2 = TName "nestedMu2" $ TMu [("Foobar", TApp maybe2 [TVar 1])]

nestedMu3 : TNamed' 0 b
nestedMu3 = TName "nestedMu3" $ TMu [("Foobar", TApp maybe2 [TVar 0])]

nestedMu4 : TNamed' 1 b
nestedMu4 = TName "nestedMu4" $ TMu [("Foobar", TApp list [TSum [TVar 0, TVar 1]])]

nestedMu5 : TNamed' 0 b
nestedMu5 = TName "nestedMu5" $ TMu [("Foobar", TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])])]

nestedMu6 : TNamed' 1 b
nestedMu6 = TName "nestedMu6" $ TMu [("Foobar", TApp nestedMu4 [TApp maybe2 [TSum [TVar 1, weakenTDef (wrap nat) _ (lteAddRight 0)]]])]

singleConstructorMu : TNamed' 0 b
singleConstructorMu = TName "Foo" $ TMu [("Bar", TProd [wrap list, def maybe])]

listOfDefs : NEList (n ** TNamed' n b)
listOfDefs = MkNEList  (0 ** bit')
                     [ (0 ** nibble)
                     , (0 ** byte')
                     , (0 ** char)
                     , (0 ** hash)
                     , (0 ** transitionId)
                     , (0 ** data')
                     , (0 ** previous)
                     , (0 ** rootTx)
                     ]
  where
  bit' : TNamed' 0 b
  bit' = TName "bit" $ TSum [T1, T1]
  nibble : TNamed' 0 b
  nibble = TName "nibble" $ powN 4 bit'
  byte' : TNamed' 0 b
  byte' = TName "byte" $ TProd [wrap nibble, wrap nibble]
  char : TNamed' 0 b
  char = TName "char" $ wrap byte'
  hash : TNamed' 0 b
  hash = TName "hash" $ wrap byte'
  transitionId : TNamed' 0 b
  transitionId = TName "transitionId" $ wrap byte'
  data' : TNamed' 0 b
  data' = TName "data" $ wrap byte'
  previous : TNamed' 0 b
  previous = TName "previous" $ wrap hash
  rootTx : TNamed' 0 b
  rootTx = TName "rootTx" $ TProd [wrap data', wrap previous]

largeTuple : TNamed' 0 b
largeTuple = TName "largeTuple" $ TProd (replicate 200 $ def bit)

{-

-- terms

nil : Ty [] Tlnat
nil = Inn (Left ())

cons : Mu [Mu [] (TSum [T1, TProd [Tnat, TVar 0]])] (TSum [T1, TVar 0]) -> Ty [] Tlnat -> Ty [] Tlnat
cons a xs = Inn (Right (a, xs))

zer : Ty tvars Tnat
zer = Inn (Left ())

suc : Ty tvars Tnat -> Ty tvars Tnat
suc x = Inn (Right x)

-}

shouldBe : Maybe Doc -> Maybe Doc -> SpecResult
shouldBe actual expected = Expectations.shouldBe (map print actual)  (map print expected)
