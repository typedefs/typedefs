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

-- listNat : TNamed 0 
-- listNat = TName "ListNat" $ TMu [("NilN", T1), ("ConsN", TProd [weakenTDef nat 1 LTEZero, TVar 0])]

parametricSynonym : TNamed 1
parametricSynonym = alias "ParSyn" maybe

parametricSynonym2 : TNamed 1
parametricSynonym2 = alias "ParSyn2" maybe2

aplusbpluscplusd : TNamed 4
aplusbpluscplusd = TName "aplusbpluscplusd" $ TSum [TVar 0, TVar 1, TVar 2, TVar 3]

oneoneoneone : TNamed 0
oneoneoneone = TName "oneoneoneone" $ TSum [T1, T1, T1, T1]

--listByte : TNamed 0
--listByte = TName  "ListByte" $ TMu [("NilC", T1), ("ConsC", TProd [weakenTDef byte 1 LTEZero, TVar 0])]

--tripleByteListnatAlpha : TDef 1
--tripleByteListnatAlpha = TName "Triple" (TProd [weakenTDef byte 1 LTEZero, weakenTDef listNat 1 LTEZero, TVar 0])

unusedFreeVars : TNamed 42
unusedFreeVars = TName "Id" (TVar 0)

voidOrUnit : TNamed 0
voidOrUnit = TName "VoidOrUnit" $ TSum [T0, T1]

nonlinear : TNamed 1
nonlinear = TName "Nonlinear" $ TProd [TVar 0, TVar 0]

nestedMu : TNamed 2
nestedMu = TName "Foo" $ TMu [("Bar", TApp list [TSum [TVar 1, TVar 2]])]

nestedMu2 : TNamed 1
nestedMu2 = TName "Foo" $ TMu [("Bar", TApp maybe2 [TVar 1])]

nestedMu3 : TNamed 0
nestedMu3 = TName "Foo" $ TMu [("Bar", TApp maybe2 [TVar 0])]

nestedMu4 : TNamed 1
nestedMu4 = TName "Foo" $ TMu [("Bar", TApp list [TSum [TVar 0, TVar 1]])]

shouldBe : Doc -> Doc -> SpecResult
shouldBe actual expected = print actual `shouldBe` print expected