module Test.Haskell

import Data.Vect 

import Typedefs
import Types
import Backend.Haskell
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

oneoneoneone : TDef 4
oneoneoneone = TName "oneoneoneone" $ TSum [TVar 0, TVar 1, TVar 2, TVar 3]

print : Doc -> String
print = toString 1 80

shouldBe : Doc -> Doc -> SpecResult
shouldBe actual expected = print actual `shouldBe` print expected

generate : TDef n -> Doc
generate = generate {lang=Haskell}

testSuite : IO ()
testSuite = spec $ do

  describe "Haskell code generation tests:" $ do

    it "bit" $ 
      generate bit
        `shouldBe` text "type" |++| text "Bit" |++| equals |++| text "Either" |++| parens empty |++| parens empty

    it "byte" $ 
      generate byte
        `shouldBe` vsep2
                    [ text "type" |++| text "Bit" |++| equals |++| text "Either" |++| parens empty |++| parens empty
                    , text "type" |++| text "Byte" |++| equals |++| tupled (replicate 8 $ text "Bit")
                    ]
        
    it "maybe" $ 
      generate maybe
        `shouldBe` text "type" |++| text "Maybe" |++| text "x0" |++| equals |++| text "Either" |++| parens empty |++| text "x0"
    
    it "list" $ 
      generate list
        `shouldBe` text "data" |++| text "List" |++| text "x0" |++|
                               equals |++| text "Nil"  |++|
                               pipe   |++| text "Cons" |++| text "x0" |++| parens (text "List" |++| text "x0")
    
    it "maybe2" $ 
      generate maybe2
        `shouldBe` text "data" |++| text "Maybe2" |++| text "x0" |++|
                               equals |++| text "Nothing" |++|
                               pipe   |++| text "Just"    |++| text "x0"
    
    it "nat" $ 
      generate nat
        `shouldBe` text "data" |++| text "Nat" |++|
                               equals |++| text "Z" |++|
                               pipe   |++| text "S" |++| text "Nat"
    
    it "listNat" $ 
      generate listNat
        `shouldBe` vsep2
                    [ text "data" |++| text "Nat" |++|
                                  equals |++| text "Z" |++|
                                  pipe   |++| text "S" |++| text "Nat"
                    , text "data" |++| text "ListNat" |++|
                                  equals |++| text "NilN" |++|
                                  pipe   |++| text "ConsN" |++| text "Nat" |++| text "ListNat"
                    ]

    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` vsep2
                    [ text "type" |++| text "Maybe" |++| text "x0" |++|
                                  equals |++| text "Either" |++| parens empty |++| text "x0"
                    , text "type" |++| text "ParSyn" |++| text "x0" |++| equals |++| text "Maybe" |++| text "x0"
                    ]

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` vsep2
                    [ text "data" |++| text "Maybe2" |++| text "x0" |++|
                                  equals |++| text "Nothing" |++|
                                  pipe   |++| text "Just" |++| text "x0"
                    , text "type" |++| text "ParSyn2" |++| text "x0" |++| equals |++| text "Maybe2" |++| text "x0"
                    ]

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` text "type" |++| text "Oneoneoneone" |++| text "x0 x1 x2 x3" |++|
                                  equals |++| text "Either" |++| text "x0" |++|
                                                parens (text "Either" |++| text "x1" |++|
                                                  parens (text "Either" |++| text "x2" |++| text "x3"))