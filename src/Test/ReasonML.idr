module Test.ReasonML

import Data.Vect 

import Typedefs
import Types
import Backend
import Backend.ReasonML

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

parametricSynonym : TDef 1
parametricSynonym = TName "parSyn" maybe

parametricSynonym2 : TDef 1
parametricSynonym2 = TName "parSyn2" maybe2

generate : TDef n -> String
generate {n} = generateDefs reasonMLBackend n


testSuite : IO ()
testSuite = spec $ do

  describe "ReasonML code generation tests:" $ do

    it "bit" $ 
      generate bit 
        `shouldBe` "\ntype bit = either(unit, unit);\n"

    it "byte" $ 
      generate byte
        `shouldBe` "\ntype bit = either(unit, unit);\n\ntype byte = (bit, bit, bit, bit, bit, bit, bit, bit);\n"
        
    it "maybe" $ 
      generate maybe
        `shouldBe` "\ntype maybe('x0) = either(unit, 'x0);\n"

    it "list" $ 
      generate list
        `shouldBe` "\ntype list('x0) = Nil | Cons('x0, list('x0));\n"
    
    it "maybe2" $ 
      generate maybe2
        `shouldBe` "\ntype maybe2('x0) = Nothing | Just('x0);\n"
    
    it "nat" $ 
      generate nat
        `shouldBe` "\ntype nat = Z | S(nat);\n"
    
    it "listNat" $ 
      generate listNat
        `shouldBe` "\ntype nat = Z | S(nat);\n\ntype listNat = NilN | ConsN(nat, listNat);\n"

    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` "\ntype maybe('x0) = either(unit, 'x0);\n\ntype parSyn('x0) = maybe('x0);\n" 

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` "\ntype maybe2('x0) = Nothing | Just('x0);\n\ntype parSyn2('x0) = maybe2('x0);\n" 