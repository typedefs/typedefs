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

generate : TNamed n -> Doc
generate (TName nm td) = generate Haskell td

boolForBit : SpecialiseEntry
boolForBit = MkSpecialiseEntry (def bit) "Bool"
                               "either (\\ () -> True) (\\ () -> False)"
                               "\\ x -> if x then Left () else Right ()"

charForByte : SpecialiseEntry
charForByte = MkSpecialiseEntry (def byte) "Char" "undefined" "undefined"

intForNat : SpecialiseEntry
intForNat = MkSpecialiseEntry (def nat) "Int"
                              "id"
                              "\\ x -> if x >= 0 then x else error \"negative number\""


generateSpecialised : Vect (S m) SpecialiseEntry -> TNamed n -> Doc
generateSpecialised se (TName nm td) = vsep2 $ map generateCode $ generateDefsSpecialised {lang=Haskell} se _ td

x0 : Doc
x0 = text "x0"

x1 : Doc
x1 = text "x1"

x2 : Doc
x2 = text "x2"

x3 : Doc
x3 = text "x3"

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
        `shouldBe` text "type" |++| text "Maybe" |++| x0 |++| equals |++| text "Either" |++| parens empty |++| x0

    let listDoc = text "data" |++| text "List" |++| x0
                  |++| equals |++| text "Nil" 
                  |++| pipe   |++| text "Cons"
                                   |++| x0 |++| parens (text "List" |++| x0)

    it "list" $
      generate list `shouldBe` listDoc

    let muMaybeDoc = text "data" |++| text "Maybe2" |++| x0
                     |++| equals |++| text "Nothing"
                     |++| pipe   |++| text "Just" |++| x0

    it "maybe2" $
      generate maybe2 `shouldBe` muMaybeDoc

    let natDoc = text "data" |++| text "Nat"
                 |++| equals |++| text "Z"
                 |++| pipe   |++| text "S" |++| text "Nat"

    it "nat" $
      generate nat `shouldBe` natDoc

    it "listNat" $
      generate listNat
        `shouldBe` vsep2
                    [ natDoc
                    , text "data" |++| text "ListNat" |++|
                                  equals |++| text "NilN" |++|
                                  pipe   |++| text "ConsN" |++| text "Nat" |++| text "ListNat"
                    ]

    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` vsep2
                    [ text "type" |++| text "Maybe" |++| x0 |++|
                                  equals |++| text "Either" |++| parens empty |++| x0
                    , text "type" |++| text "ParSyn" |++| x0 |++| equals |++| text "Maybe" |++| x0
                    ]

    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` vsep2
                    [ text "data" |++| text "Maybe2" |++| x0 |++|
                                  equals |++| text "Nothing" |++|
                                  pipe   |++| text "Just" |++| x0
                    , text "type" |++| text "ParSyn2" |++| x0 |++| equals |++| text "Maybe2" |++| x0
                    ]

    it "aplusbpluscplusd" $
      generate aplusbpluscplusd
        `shouldBe` text "type" |++| text "Aplusbpluscplusd" |++| hsep [x0,x1,x2,x3] |++|
                                  equals |++| text "Either" |++| x0 |++|
                                                parens (text "Either" |++| x1 |++|
                                                  parens (text "Either" |++| text "x2" |++| text "x3"))

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` text "type" |++| text "Oneoneoneone" |++|
                                  equals |++| text "Either" |++| text "()" |++|
                                                parens (text "Either" |++| text "()" |++|
                                                  parens (text "Either" |++| text "()" |++| text "()"))

    it "unusedFreeVars" $
      generate unusedFreeVars
        `shouldBe` text "type" |++| text "Id" |++| x0
                      |++| equals |++| x0 -- not "\ntype Id x0 x1 ... x42 = x0\n"

    it "void or unit" $
      generate voidOrUnit
        `shouldBe` text "type" |++| text "VoidOrUnit"
                   |++| equals |++| text "Either" |++| text "Void" |++| text "()"

    it "nonlinear variable usage" $
      generate nonlinear
        `shouldBe` text "type" |++| text "Nonlinear" |++| x0
                   |++| equals |++| tupled [x0, x0]

    it "nested Mu (Foo/List/Either)" $
      generate nestedMu
        `shouldBe` vsep2
                    [ listDoc 
                    , text "data" |++| text "Foo" |++| hsep [x0,x1]
                      |++| equals |++| text "Bar"
                                       |++| parens (text "List" |++| parens (text "Either" |++| hsep [x0,x1]))
                    ]

    it "nested Mu 2 (Foo/Maybe/Alpha)" $
      generate nestedMu2
        `shouldBe` vsep2
                    [ muMaybeDoc
                    , text "data" |++| text "Foo" |++| x0
                      |++| equals |++| text "Bar"
                                       |++| parens (text "Maybe2" |++| x0) 
                    ]

    it "nested Mu 3 (Foo/Maybe/Foo)" $
      generate nestedMu3
        `shouldBe` vsep2
                    [ muMaybeDoc
                    , text "data" |++| text "Foo"
                      |++| equals |++| text "Bar"
                                       |++| parens (text "Maybe2" |++| text "Foo")
                    ]

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
                        , text "type" |++| text "Triple" |++| x0
                          |++| equals |++| tupled [text "Char", text "ListNat", x0]
                        ]
