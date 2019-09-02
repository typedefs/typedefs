module Typedefs.Test.HaskellTests

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.Backend
import Typedefs.Backend.Utils
import Typedefs.Backend.Haskell

import Typedefs.Test
import Typedefs.Test.HaskellStrings

import Text.PrettyPrint.WL
import Specdris.Spec

import Data.NEList
import Data.Vect

%access public export

generate : TNamed n -> Maybe Doc
generate {n} tn = eitherToMaybe $ generateDefs Haskell $ singleton (n ** tn)

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

    it "bit" $
      generate bit
        `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, bitDoc ])


    it "byte" $
      generate byte
        `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, byteDoc ])


    it "maybe" $
      generate maybe
        `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, maybeDoc ])


    it "list" $
      generate list `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, listDoc])


    it "maybe2" $
      generate maybe2 `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, muMaybeDoc])


    it "nat" $
      generate nat `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, natDoc ])


    it "listNat" $
      generate listNat
        `shouldBe` (Just $ vsep2 [ preamble {def = Haskell}, listNatDoc ])


    it "parametricSynonym" $
      generate parametricSynonym
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , parametricDoc
                      ])


    it "parametricSynonym2" $
      generate parametricSynonym2
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , parametric2Doc
                      ])


    it "aplusbpluscplusd" $
      generate aplusbpluscplusd
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , aplusbpluscplusdDoc
                      ])


    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , oneoneoneoneDoc
                      ])


    it "unusedFreeVars" $
      generate unusedFreeVars
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , unusedFreeVarsDoc
                      ])


    it "void or unit" $
      generate voidOrUnit
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , voidOrUnitDoc
                      ])


    it "nonlinear variable usage" $
      generate nonlinear
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , nonlinearDoc
                      ])


    it "listAlphaOrBeta" $
      generate listAlphaOrBeta
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , listAlphaOrBetaDoc
                      ])


    it "listBitOrByte" $
      generate listBitOrByte
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , listBitOrByteDoc
                      ])


    it "nested Mu 1: List(Either(Alpha, Beta))" $
      generate nestedMu1
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , nestedMu1Doc
                      ])


    it "nested Mu 2: Maybe2(Alpha)" $
      generate nestedMu2
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , nestedMu2Doc
                      ])


    it "nested Mu 3: Maybe2(Mu)" $
      generate nestedMu3
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , nestedMu3Doc
                      ])


    it "nested mu 4: List(Either (Mu, Alpha))" $
      generate nestedMu4
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , nestedMu4Doc
                      ])


    it "nested mu 5: AnonList(Mu)" $
      generate nestedMu5
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , nestedMu5Doc
                      ])


    it "single constructor mu" $
      generate singleConstructorMu
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , singleConstructorMuDoc
                      ])

    it "list of definitions [bit, nibble, byte, char, hash, transitionId, data, previous, rootTx]" $
      (eitherToMaybe $ generateDefs Haskell listOfDefs)
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , listOfDefsDoc
                      ])

{-
    it "large tuple" $
      generate largeTuple
        `shouldBe` (Just $ vsep2
                      [ preamble {def = Haskell}
                      , largeTupleDoc
                      ])

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
