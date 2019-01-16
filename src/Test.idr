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
{-
list : TDef 1
list = TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

maybe2 : TDef 1
maybe2 = TMu "Maybe2" [("Nothing", T1), ("Just", TVar 1)]

nat : TDef 0
nat = TMu "Nat" [("Z", T1), ("S", TVar 0)]

listNat : TDef 0 
listNat = TMu "ListNat" [("NilN", T1), ("ConsN", TProd [weakenTDef nat 1 LTEZero, TVar 0])]
-}
parametricSynonym : TNamed 1
parametricSynonym = alias "ParSyn" maybe

--parametricSynonym2 : TDef 1
--parametricSynonym2 = TName "ParSyn2" maybe2

aplusbpluscplusd : TNamed 4
aplusbpluscplusd = TName "aplusbpluscplusd" $ TSum [TVar 0, TVar 1, TVar 2, TVar 3]

oneoneoneone : TNamed 0
oneoneoneone = TName "oneoneoneone" $ TSum [T1, T1, T1, T1]
{-
listByte : TDef 0
listByte = TMu "ListByte" [("NilC", T1), ("ConsC", TProd [weakenTDef byte 1 LTEZero, TVar 0])]

tripleByteListnatAlpha : TDef 1
tripleByteListnatAlpha = TName "Triple" (TProd [weakenTDef byte 1 LTEZero, weakenTDef listNat 1 LTEZero, TVar 0])
-}
unusedFreeVars : TNamed 42
unusedFreeVars = TName "Id" (TVar 0)

voidOrUnit : TNamed 0
voidOrUnit = TName "VoidOrUnit" $ TSum [T0, T1]

nonlinear : TNamed 1
nonlinear = TName "Nonlinear" $ TProd [TVar 0, TVar 0]
{-
nestedMu : TDef 2
nestedMu = TMu "Foo" [("Bar", list `ap` [TSum [TVar 1, TVar 2]])]

nestedMu2 : TDef 1
nestedMu2 = TMu "Foo" [("Bar", maybe2 `ap` [TVar 1])]

nestedMu3 : TDef 0
nestedMu3 = TMu "Foo" [("Bar", maybe2 `ap` [TVar 0])]
-}
shouldBe : Doc -> Doc -> SpecResult
shouldBe actual expected = print actual `shouldBe` print expected