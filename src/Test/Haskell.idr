module Test.Haskell

import Types
import Typedefs

import Backend
import Backend.Utils
import Backend.Haskell

import Text.PrettyPrint.WL
import Specdris.Spec

import Data.Vect
import Test

%access public export

generate : TDef n -> Doc
generate = generate {lang=Haskell}

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

generateSpecialised : Vect (S m) SpecialiseEntry -> TDef n -> Doc
generateSpecialised se td = vsep2 $ map generateCode $ generateDefsSpecialised {lang=Haskell} se _ td

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

    it "aplusbpluscplusd" $
      generate aplusbpluscplusd
        `shouldBe` text "type" |++| text "Aplusbpluscplusd" |++| text "x0 x1 x2 x3" |++|
                                  equals |++| text "Either" |++| text "x0" |++|
                                                parens (text "Either" |++| text "x1" |++|
                                                  parens (text "Either" |++| text "x2" |++| text "x3"))

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` text "type" |++| text "Oneoneoneone" |++|
                                  equals |++| text "Either" |++| text "()" |++|
                                                parens (text "Either" |++| text "()" |++|
                                                  parens (text "Either" |++| text "()" |++| text "()"))

    it "unusedFreeVars" $
      generate unusedFreeVars
        `shouldBe` text "type" |++| text "Id" |++| text "x0"
                      |++| equals |++| text "x0" -- not "\ntype Id x0 x1 ... x42 = x0\n"

    it "void or unit" $
      generate voidOrUnit
        `shouldBe` text "type" |++| text "VoidOrUnit"
                   |++| equals |++| text "Either" |++| text "Void" |++| text "()"

  describe "Haskell specialised types tests:" $ do

    let boolForBitDoc = text "type" |++| text "Byte"
                        |++| equals |++| tupled (replicate 8 $ text "Bool")

    it "bit" $
      generateSpecialised [boolForBit] byte
        `shouldBe` boolForBitDoc

    it "byte" $
      generateSpecialised [charForByte, boolForBit] listByte
        `shouldBe` text "data" |++| text "ListByte"
                      |++| equals |++| text "NilC"
                      |++| pipe   |++| text "ConsC" |++| text "Char" |++| text "ListByte"

    it "byteWrongOrder" $
      generateSpecialised [boolForBit, charForByte] listByte
        `shouldBe` vsep2
                        [ boolForBitDoc
                        , text "data" |++| text "ListByte"
                          |++| equals |++| text "NilC"
                          |++| pipe   |++| text "ConsC" |++| text "Byte" |++| text "ListByte"
                        ]

    it "triple with Byte |-> Char, Listnat, Alpha" $
      generateSpecialised [charForByte, boolForBit, intForNat] tripleByteListnatAlpha
        `shouldBe` vsep2
                        [ text "data" |++| text "ListNat"
                          |++| equals |++| text "NilN"
                          |++| pipe   |++| text "ConsN" |++| text "Int" |++| text "ListNat"
                        , text "type" |++| text "Triple" |++| text "x0"
                          |++| equals |++| tupled [text "Char", text "ListNat", text "x0"]
                        ]
