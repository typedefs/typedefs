module Test.Parse

import TParsec
import TParsec.Running

import Typedefs
import Parse

import Specdris.Spec

%access public export

testSuite : IO ()
testSuite = spec $ do

  describe "well-formed terms" $ do

    it "\"0\"" $ do
      showTDef "0"
        `shouldBe` "Just (0 ** 0)"

    it "\"1\"" $ do
      showTDef "1"
        `shouldBe` "Just (0 ** 1)"

    it "\"(var 123)\"" $ do
      showTDef "(var 123)"
        `shouldBe` "Just (124 ** {123})"

    it "\"(var 0)\"" $ do
      showTDef "(var 0)"
        `shouldBe` "Just (1 ** {0})"

    it "\"(var 0) \"" $ do
      showTDef "(var 0) "
        `shouldBe` "Just (1 ** {0})"

    it "\"(mu list (cons (* (var 1) (var 0))))\"" $ do
      showTDef "(mu list (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [cons: ({1} * {0})])"

    it "\"(mu list (nil 1) (cons (* (var 1) (var 0))))\"" $ do
      showTDef "(mu list (nil 1) (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(mu list (nil 1) (cons (* (var 1) (var 0)) ))\"" $ do
      showTDef "(mu list (nil 1) (cons (* (var 1) (var 0)) ))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(* 1 1)\"" $ do
      showTDef "(* 1 1)"
        `shouldBe` "Just (0 ** (1 * 1))"

    it "\"(+ 1 0)\"" $ do
      showTDef "(+ 1 0)"
        `shouldBe` "Just (0 ** (1 + 0))"

    it "\"(+ 1 (* (var 0) 0))\"" $ do
      showTDef "(+ 1 (* (var 0) 0))"
        `shouldBe` "Just (1 ** (1 + ({0} * 0)))"

    it "\"(+ 1 1 0)\"" $ do
      showTDef "(+ 1 1 0)"
        `shouldBe` "Just (0 ** (1 + 1 + 0))"

    it "\"(+ 1 1 0 (* 1 0))\"" $ do
      showTDef "(+ 1 1 0 (* 1 0))"
        `shouldBe` "Just (0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "ill-formed terms" $ do

    it "\"(*)\" - <2 operands" $ do
      showTDef "(*)"
        `shouldBe` "Nothing"

    it "\"(+ 1)\" - <2 operands" $ do
      showTDef "(+ 1)"
        `shouldBe` "Nothing"

    it "\"(mu list (nil 1))\" - no free variables under mu" $ do
      showTDef "(mu list (nil 1))"
        `shouldBe` "Nothing"

    it "\"(+ 1 * 1 0)\" - malformed" $ do
      showTDef "(+ 1 * 1 0)"
        `shouldBe` "Nothing"
