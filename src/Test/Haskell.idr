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
generate = generate Haskell
{-
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
-}
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
    let bitDoc = text "type" |++| text "Bit" |++| equals |++| text "Either" |++| parens empty |++| parens empty

    it "bit" $
      generate bit
        `shouldBe` bitDoc

    let byteDoc = text "type" |++| text "Byte" |++| equals |++| tupled (replicate 8 $ text "Bit")

    it "byte" $
      generate byte
        `shouldBe` vsep2
                    [ bitDoc
                    , byteDoc
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

    let listAlphaOrBetaDoc =
      vsep2
        [ listDoc
        , text "type" |++| text "ListAlphaOrBeta" |++| hsep [x0,x1]
          |++| equals |++| text "List" |++| parens (text "Either" |++| hsep [x0,x1])
        ]

    it "listAlphaOrBeta" $
      generate listAlphaOrBeta `shouldBe` listAlphaOrBetaDoc

    it "listBitOrByte" $
      generate listBitOrByte
        `shouldBe` vsep2
                    [ byteDoc
                    , bitDoc
                    , listAlphaOrBetaDoc
                    , text "type" |++| text "ListBitOrByte"
                      |++| equals |++| text "ListAlphaOrBeta" |++| text "Bit" |++| text "Byte"
                    ]

    it "nested Mu 1: List(Either(Alpha, Beta))" $
      generate nestedMu1
        `shouldBe` vsep2
                    [ listDoc
                    , text "data" |++| text "NestedMu1" |++| hsep [x0,x1]
                      |++| equals |++| text "Foobar"
                                       |++| parens (text "List" |++| parens (text "Either" |++| hsep [x0,x1]))
                    ]

    it "nested Mu 2: Maybe2(Alpha)" $
      generate nestedMu2
        `shouldBe` vsep2
                    [ muMaybeDoc
                    , text "data" |++| text "NestedMu2" |++| x0
                      |++| equals |++| text "Foobar"
                                       |++| parens (text "Maybe2" |++| x0) 
                    ]

    it "nested Mu 3: Maybe2(Mu)" $
      generate nestedMu3
        `shouldBe` vsep2
                    [ muMaybeDoc
                    , text "data" |++| text "NestedMu3"
                      |++| equals |++| text "Foobar"
                                       |++| parens (text "Maybe2" |++| text "NestedMu3")
                    ]

    let nestedMu4Doc =
      vsep2
        [ listDoc
        , text "data" |++| text "NestedMu4" |++| x0
          |++| equals |++| text "Foobar"
                           |++| parens (text "List"
                                |++| parens (text "Either" 
                                     |++| parens (text "NestedMu4" |++| x0)
                                     |++| x0))
        ]

    it "nested Mu 4: List(Either (Mu, Alpha))" $
      generate nestedMu4 `shouldBe` nestedMu4Doc

    it "nested Mu 5: NilCons(Mu)" $ 
      generate nestedMu5
        `shouldBe` vsep2
                    [ text "data" |++| text "NilCons" |++| x0
                      |++| equals |++| text "Nil" 
                      |++| pipe   |++| text "Cons"
                                       |++| x0 |++| parens (text "NilCons" |++| x0)
                    , text "data" |++| text "NestedMu5" |++| hsep [x0]
                      |++| equals |++| text "Foobar"
                                       |++| parens (text "NilCons" |++| parens (text "NestedMu5" |++| x0))
                    ]

    it "nested Mu 6: NestedMu4(Maybe2(Either(Alpha, Nat)))" $
      generate nestedMu6
        `shouldBe` vsep2
                    [ natDoc
                    , muMaybeDoc
                    , nestedMu4Doc
                    , text "data" |++| text "NestedMu6" |++| x0
                      |++| equals |++| text "Foobar"
                                       |++| parens (text "NestedMu4"
                                            |++| parens (text "Maybe2"
                                                 |++| parens (text "Either"
                                                      |++| x0
                                                      |++| text "Nat")))
                    ]

{-
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
-}