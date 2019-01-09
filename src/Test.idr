module Test

import Data.Vect 

import Typedefs
import Types
import Backend.Utils

import Specdris.Spec
import Text.PrettyPrint.WL

%access public export

bit : TDef 0
bit = TName "Bit" $ TSum [T1, T1]

byte : TDef 0
byte = TName "Byte" $ pow 8 bit

maybe : TDef 1
maybe = TName "Maybe" $  TSum [T1, TVar 0]

list : TDef 1
list = TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]

maybe2 : TDef 1
maybe2 = TMu "Maybe2" [("Nothing", T1), ("Just", TVar 1)]

nat : TDef 0
nat = TMu "Nat" [("Z", T1), ("S", TVar 0)]

listNat : TDef 0 
listNat = TMu "ListNat" [("NilN", T1), ("ConsN", TProd [weakenTDef nat 1 LTEZero, TVar 0])]

parametricSynonym : TDef 1
parametricSynonym = TName "ParSyn" maybe

parametricSynonym2 : TDef 1
parametricSynonym2 = TName "ParSyn2" maybe2

aplusbpluscplusd : TDef 4
aplusbpluscplusd = TName "aplusbpluscplusd" $ TSum [TVar 0, TVar 1, TVar 2, TVar 3]

oneoneoneone : TDef 0
oneoneoneone = TName "oneoneoneone" $ TSum [T1, T1, T1, T1]

listByte : TDef 0
listByte = TMu "ListByte" [("NilC", T1), ("ConsC", TProd [weakenTDef byte 1 LTEZero, TVar 0])]

tripleByteListnatAlpha : TDef 1
tripleByteListnatAlpha = TName "Triple" (TProd [weakenTDef byte 1 LTEZero, weakenTDef listNat 1 LTEZero, TVar 0])

unusedFreeVars : TDef 42
unusedFreeVars = TName "Id" (TVar 0)

voidOrUnit : TDef 0
voidOrUnit = TName "VoidOrUnit" $ TSum [T0, T1]

nonlinear : TDef 1
nonlinear = TName "Nonlinear" $ TProd [TVar 0, TVar 0]

shouldBe : Doc -> Doc -> SpecResult
shouldBe actual expected = print actual `shouldBe` print expected