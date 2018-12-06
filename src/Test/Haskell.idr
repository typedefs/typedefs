module Test.Haskell

import Data.Vect 

import Typedefs
import Types
import Backend
import Backend.Haskell

import Specdris.Spec

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

listByte : TDef 0
listByte = TMu "ListByte" [("NilC", T1), ("ConsC", TProd [weakenTDef byte 1 LTEZero, TVar 0])]

charlistNatalphaTriples : TDef 1
charlistNatalphaTriples = TName "Triple" (TProd [weakenTDef byte 1 LTEZero, weakenTDef listNat 1 LTEZero, TVar 0])

parametricSynonym : TDef 1
parametricSynonym = TName "ParSyn" maybe

parametricSynonym2 : TDef 1
parametricSynonym2 = TName "ParSyn2" maybe2

boolForBit : SpecialiseEntry
boolForBit = MkSpecialiseEntry bit "Bool"
                               "either (\\ () -> True) (\\ () -> False)"
                               "\\ x -> if x then Left () else Right ()"

charForByte : SpecialiseEntry
charForByte = MkSpecialiseEntry byte "Char" "undefined" "undefined"

intForNat : SpecialiseEntry
intForNat = MkSpecialiseEntry nat "Int"
                              "id"
                              "\\ x -> if x >= 0 then x else error \"negative number\""

generate : TDef n -> String
generate {n} = generateDefs haskellBackend n

generateSpecialised : Vect (S m) SpecialiseEntry -> TDef n -> String
generateSpecialised se td = generateDefsSpecialised haskellBackend se _ td

testSuite : IO ()
testSuite = spec $ do

  describe "Haskell code generation tests:" $ do

    it "bit" $ 
      generate bit 
        `shouldBe` "\ntype Bit = Either () ()\n"

    it "byte" $ 
      generate byte
        `shouldBe` "\ntype Bit = Either () ()\n\ntype Byte = (Bit, Bit, Bit, Bit, Bit, Bit, Bit, Bit)\n"
        
    it "maybe" $ 
      generate maybe
        `shouldBe` "\ntype Maybe x0 = Either () x0\n"
    
    it "list" $ 
      generate list
        `shouldBe` "\ndata List x0 = Nil | Cons x0 (List x0)\n"
    
    it "maybe2" $ 
      generate maybe2
        `shouldBe` "\ndata Maybe2 x0 = Nothing | Just x0\n"
    
    it "nat" $ 
      generate nat
        `shouldBe` "\ndata Nat = Z | S Nat\n"
    
    it "listNat" $ 
      generate listNat
        `shouldBe` "\ndata Nat = Z | S Nat\n\ndata ListNat = NilN | ConsN Nat ListNat\n"

    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` "\ntype Maybe x0 = Either () x0\n\ntype ParSyn x0 = Maybe x0\n"

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` "\ndata Maybe2 x0 = Nothing | Just x0\n\ntype ParSyn2 x0 = Maybe2 x0\n"

  describe "Haskell specialised types tests:" $ do

    it "bit" $
      generateSpecialised [boolForBit] byte
        `shouldBe` "\ntype Byte = (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)\n"

    it "byte" $
      generateSpecialised [charForByte, boolForBit] listByte
        `shouldBe` "\ndata ListByte = NilC | ConsC Char ListByte\n"

    it "byteWrongOrder" $
      generateSpecialised [boolForBit, charForByte] listByte
        `shouldBe` "\ntype Byte = (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)\n\ndata ListByte = NilC | ConsC Byte ListByte\n"

    it "listnatTriple" $
      generateSpecialised [charForByte, boolForBit, intForNat] charlistNatalphaTriples
        `shouldBe` "\ndata ListNat = NilN | ConsN Int ListNat\n\ntype Triple x0 = (Char, ListNat, x0)\n"

