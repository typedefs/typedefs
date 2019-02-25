module Test.ReasonML

import Types
import Typedefs

import Backend
import Backend.Utils
import Backend.ReasonML

import Text.PrettyPrint.WL
import Specdris.Spec

import Data.Vect
import Test

%access public export

x0 : Doc
x0 = text "'x0"

x1 : Doc
x1 = text "'x1"

x2 : Doc
x2 = text "'x2"

x3 : Doc
x3 = text "'x3"

eitherDoc : Doc
eitherDoc = text "type" |++| text "either" |+| tupled [x0,x1]
            |++| equals |++| text "Left" |+| parens x0 |++| pipe |++| text "Right" |+| parens x1 |+| semi

generate : TNamed n -> Doc
generate = generate ReasonML

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
{-
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

    let listDoc = text "type" |++| text "list" |+| parens x0
                  |++| equals |++| text "Nil"
                  |++| pipe   |++| text "Cons" |+| tupled [x0, text "list" |+| parens x0]
                  |+| semi

    it "list" $
      generate list `shouldBe` listDoc

    let muMaybeDoc = text "type" |++| text "maybe2" |+| parens x0
                     |++| equals |++| text "Nothing"
                     |++| pipe   |++| text "Just" |+| parens x0
                     |+| semi

    it "maybe2" $
      generate maybe2 `shouldBe` muMaybeDoc

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
                    [ muMaybeDoc
                    , text "type" |++| text "parSyn2" |+| parens x0
                      |++| equals |++| text "maybe2" |+| parens x0
                      |+| semi
                    ]

    it "aplusbpluscplusd" $
      generate aplusbpluscplusd
        `shouldBe` vsep2
                    [ eitherDoc
                    , text "type" |++| text "aplusbpluscplusd" |+| tupled [x0,x1,x2,x3]
                      |++| equals |++| text "either" |+| tupled [x0,
                                          text "either" |+| tupled [x1,
                                            text "either" |+| tupled [x2, x3]]]
                      |+| semi
                    ]

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` vsep2
                    [ eitherDoc
                    , text "type" |++| text "oneoneoneone"
                      |++| equals |++| text "either" |+| tupled [text "unit",
                                          text "either" |+| tupled [text "unit",
                                            text "either" |+| tupled [text "unit", text "unit"]]]
                      |+| semi
                    ]

    it "unusedFreeVars" $
      generate unusedFreeVars
        `shouldBe` text "type" |++| text "id" |+| parens x0
                      |++| equals |++| x0
                      |+| semi -- not "\ntype id('x0, 'x1, ..., 'x41) = 'x0\n"

    it "void or unit" $
      generate voidOrUnit
        `shouldBe` vsep2
                    [ text "type" |++| text "void" |+| semi
                    , eitherDoc
                    , text "type" |++| text "voidOrUnit"
                      |++| equals |++| text "either" |+| tupled [text "void", text "unit"]
                      |+| semi
                    ]

    it "nonlinear variable usage" $
      generate nonlinear
        `shouldBe` text "type" |++| text "nonlinear" |+| parens x0
                   |++| equals |++| tupled [x0, x0]
                   |+| semi

    it "nested Mu (Foo/List/Either)" $
      generate nestedMu
        `shouldBe` vsep2
                    [ listDoc
                    , eitherDoc
                    , text "type" |++| text "foo" |+| tupled [x0,x1]
                      |++| equals |++| text "Bar"
                                       |++| parens (text "list" |++| parens (text "either" |+| tupled [x0,x1]))
                      |+| semi
                    ]

    it "nested Mu 2 (Foo/Maybe/Alpha)" $
      generate nestedMu2
        `shouldBe` vsep2
                    [ muMaybeDoc
                    , text "type" |++| text "foo" |+| parens x0
                      |++| equals |++| text "Bar"
                                       |+| parens (text "maybe2" |+| parens x0)
                      |+| semi
                    ]

    it "nested Mu 3 (Foo/Maybe/Foo)" $
      generate nestedMu3
        `shouldBe` vsep2
                    [ muMaybeDoc
                    , text "type" |++| text "foo"
                      |++| equals |++| text "Bar"
                                       |+| parens (text "maybe2" |+| parens (text "foo"))
                      |+| semi
                    ]
-}
