module Test.ReasonML

import Data.Vect 

import Typedefs
import Types
import Backend.ReasonML
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
parametricSynonym = TName "parSyn" maybe

parametricSynonym2 : TDef 1
parametricSynonym2 = TName "parSyn2" maybe2

x0 : Doc
x0 = text "'x0"

x1 : Doc
x1 = text "'x1"

eitherDoc : Doc
eitherDoc = text "type" |++| text "either" |+| tupled [x0,x1]
            |++| equals |++| text "Left" |+| parens x0 |++| pipe |++| text "Right" |+| parens x1 |+| semi

print : Doc -> String
print = toString 1 80

shouldBe : Doc -> Doc -> SpecResult
shouldBe actual expected = print actual `shouldBe` print expected

generate : TDef n -> Doc
generate {n} = generate {lang=ReasonML}

testSuite : IO ()
testSuite = spec $ do

  describe "ReasonML code generation tests:" $ do
    let bitDoc = vsep2
                  [ eitherDoc
                  , text "type" |++| text "bit"
                    |++| equals |++| text "either" |+| tupled (replicate 2 (text "unit")) |+| semi
                  ]

    it "bit" $ 
      generate bit `shouldBe` bitDoc

    it "byte" $ 
      generate byte
        `shouldBe` vsep2
                    [ bitDoc
                    , text "type" |++| text "byte"
                      |++| equals |++| tupled (replicate 8 (text "bit"))
                      |+| semi
                    ]
    
    let maybeDoc = vsep2
                     [ eitherDoc
                     , text "type" |++| text "maybe" |+| parens x0
                       |++| equals |++| text "either" |+| tupled [text "unit", x0]
                       |+| semi
                     ]

    it "maybe" $ 
      generate maybe `shouldBe` maybeDoc

    it "list" $ 
      generate list
        `shouldBe` text "type" |++| text "list" |+| parens x0
                   |++| equals |++| text "Nil"
                   |++| pipe   |++| text "Cons" |+| tupled [x0, text "list" |+| parens x0]
                   |+| semi

    let maybe2Doc = text "type" |++| text "maybe2" |+| parens x0
                    |++| equals |++| text "Nothing"
                    |++| pipe   |++| text "Just" |+| parens x0
                    |+| semi

    it "maybe2" $ 
      generate maybe2 `shouldBe` maybe2Doc

    let natDoc = text "type" |++| text "nat"
                 |++| equals |++| text "Z"
                 |++| pipe   |++| text "S" |+| parens (text "nat")
                 |+| semi

    it "nat" $ 
      generate nat `shouldBe` natDoc

    it "listNat" $ 
      generate listNat
        `shouldBe` vsep2
                    [ natDoc
                    , text "type" |++| text "listNat"
                      |++| equals |++| text "NilN"
                      |++| pipe   |++| text "ConsN" |+| tupled [ text "nat", text "listNat" ]
                      |+| semi
                    ]

    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` vsep2
                    [ maybeDoc
                    , text "type" |++| text "parSyn" |+| parens x0
                      |++| equals |++| text "maybe" |+| parens x0
                      |+| semi
                    ]

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` vsep2
                    [ maybe2Doc
                    , text "type" |++| text "parSyn2" |+| parens x0
                      |++| equals |++| text "maybe2" |+| parens x0
                      |+| semi
                    ]