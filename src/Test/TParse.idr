module Test.TParse

import TParsec
import TParsec.Running

import Typedefs
import TParseTDef

import Specdris.Spec

%access public export

showTDef : String -> String
showTDef str =
  show $ parseMaybe str tdef

testSuite : IO ()
testSuite = spec $ do

  describe "well-formed terms" $ do

    it "\"Void\"" $ do
      showTDef "Void"
        `shouldBe` "Just (0 ** 0)"

    it "\"Unit\"" $ do
      showTDef "Unit"
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

    it "\"(mu list (nil Unit) (cons (* (var 1) (var 0))))\"" $ do
      showTDef "(mu list (nil Unit) (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(mu list (nil Unit) (cons (* (var 1) (var 0)) ))\"" $ do
      showTDef "(mu list (nil Unit) (cons (* (var 1) (var 0)) ))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(* Unit Unit)\"" $ do
      showTDef "(* Unit Unit)"
        `shouldBe` "Just (0 ** (1 * 1))"

    it "\"(+ Unit Void)\"" $ do
      showTDef "(+ Unit Void)"
        `shouldBe` "Just (0 ** (1 + 0))"

    it "\"(+ Unit (* (var 0) Void))\"" $ do
      showTDef "(+ Unit (* (var 0) Void))"
        `shouldBe` "Just (1 ** (1 + ({0} * 0)))"

    it "\"(+ Unit Unit Void)\"" $ do
      showTDef "(+ Unit Unit Void)"
        `shouldBe` "Just (0 ** (1 + 1 + 0))"

    it "\"(+ Unit Unit Void (* Unit Void))\"" $ do
      showTDef "(+ Unit Unit Void (* Unit Void))"
        `shouldBe` "Just (0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "ill-formed terms" $ do

    it "\"(*)\" - <2 operands" $ do
      showTDef "(*)"
        `shouldBe` "Nothing"

    it "\"(+ Unit)\" - <2 operands" $ do
      showTDef "(+ Unit)"
        `shouldBe` "Nothing"

    it "\"(mu list (nil Unit))\" - no free variables under mu" $ do
      showTDef "(mu list (nil Unit))"
        `shouldBe` "Nothing"

    it "\"(+ Unit * Unit Void)\" - malformed" $ do
      showTDef "(+ Unit * Unit Void)"
        `shouldBe` "Nothing"
