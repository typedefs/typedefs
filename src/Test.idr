module Test

import Data.Vect 

import Typedefs
import Types
import Backend.Utils

import Specdris.Spec
import Text.PrettyPrint.WL

%default total
%access public export

bit : TNamed 0
bit = TName "Bit" $ TSum [T1, T1]

byte : TNamed 0
byte = TName "Byte" $ powN 8 bit

maybe : TNamed 1
maybe = TName "Maybe" $  TSum [T1, TVar 0]

bar : TNamed 2
bar = TName "Bar" $ TProd [TVar 1, TVar 0]

foo : TNamed 3
foo = TName "Foo" $ TApp bar [TProd [TVar 1, TVar 2], TVar 0]

list : TNamed 1
list = TName "List" $ TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

maybe2 : TNamed 1
maybe2 = TName "Maybe2" $ TMu [("Nothing", T1), ("Just", TVar 1)]

nat : TNamed 0
nat = TName "Nat" $ TMu [("Z", T1), ("S", TVar 0)]

listNat : TNamed 0 
listNat = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [weakenTDef (wrap nat) 1 LTEZero, TVar 0])]

parametricSynonym : TNamed 1
parametricSynonym = alias "ParSyn" maybe

parametricSynonym2 : TNamed 1
parametricSynonym2 = alias "ParSyn2" maybe2

aplusbpluscplusd : TNamed 4
aplusbpluscplusd = TName "aplusbpluscplusd" $ TSum [TVar 0, TVar 1, TVar 2, TVar 3]

oneoneoneone : TNamed 0
oneoneoneone = TName "oneoneoneone" $ TSum [T1, T1, T1, T1]

listByte : TNamed 0
listByte = TName  "ListByte" $ TMu [("NilC", T1), ("ConsC", TProd [weakenTDef (wrap byte) 1 LTEZero, TVar 0])]

tripleByteListnatAlpha : TNamed 1
tripleByteListnatAlpha = TName "Triple" (TProd [weakenTDef (wrap byte) 1 LTEZero, weakenTDef (wrap listNat) 1 LTEZero, TVar 0])

unusedFreeVars : TNamed 42
unusedFreeVars = TName "Id" (TVar 0)

voidOrUnit : TNamed 0
voidOrUnit = TName "VoidOrUnit" $ TSum [T0, T1]

nonlinear : TNamed 1
nonlinear = TName "Nonlinear" $ TProd [TVar 0, TVar 0]

listAlphaOrBeta : TNamed 2
listAlphaOrBeta = TName "listAlphaOrBeta" $ TApp list [TSum [TVar 0, TVar 1]]

listBitOrByte : TNamed 0
listBitOrByte = TName "listBitOrByte" $ TApp listAlphaOrBeta [wrap bit, wrap byte]

nestedMu1 : TNamed 2
nestedMu1 = TName "nestedMu1" $ TMu [("Foobar", shiftVars (def listAlphaOrBeta))]

nestedMu2 : TNamed 1
nestedMu2 = TName "nestedMu2" $ TMu [("Foobar", TApp maybe2 [TVar 1])]

nestedMu3 : TNamed 0
nestedMu3 = TName "nestedMu3" $ TMu [("Foobar", TApp maybe2 [TVar 0])]

nestedMu4 : TNamed 1
nestedMu4 = TName "nestedMu4" $ TMu [("Foobar", TApp list [TSum [TVar 0, TVar 1]])]

nestedMu5 : TNamed 0
nestedMu5 = TName "nestedMu5" $ TMu [("Foobar", TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])])]

nestedMu6 : TNamed 1
nestedMu6 = TName "nestedMu6" $ TMu [("Foobar", TApp nestedMu4 [TApp maybe2 [TSum [TVar 1, weakenTDef (wrap nat) _ (lteAddRight 0)]]])]

shouldBe : Doc -> Doc -> SpecResult
shouldBe actual expected = print actual `shouldBe` print expected