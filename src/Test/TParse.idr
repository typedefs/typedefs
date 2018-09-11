module Test.TParse

import TParsec
import TParsec.Running

import Typedefs
import TParseTDef

import Specdris.Spec

%access public export

showAST : String -> String
showAST str =
  show $ parseMaybe str tdef

testSuite : IO ()
testSuite = spec $ do

  describe "well-formed terms" $ do

    it "\"Void\"" $ do
      showAST "Void"
        `shouldBe` "Just (0 ** 0)"

    it "\"Unit\"" $ do
      showAST "Unit"
        `shouldBe` "Just (0 ** 1)"

    it "\"(var 123)\"" $ do
      showAST "(var 123)"
        `shouldBe` "Just (124 ** {123})"

    it "\"(var 0)\"" $ do
      showAST "(var 0)"
        `shouldBe` "Just (1 ** {0})"

    it "\"(var 0) \"" $ do
      showAST "(var 0) "
        `shouldBe` "Just (1 ** {0})"

    it "\"(mu list (cons (* (var 1) (var 0))))\"" $ do
      showAST "(mu list (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [cons: ({1} * {0})])"

    it "\"(mu list (nil Unit) (cons (* (var 1) (var 0))))\"" $ do
      showAST "(mu list (nil Unit) (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(mu list (nil Unit) (cons (* (var 1) (var 0)) ))\"" $ do
      showAST "(mu list (nil Unit) (cons (* (var 1) (var 0)) ))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(* Unit Unit)\"" $ do
      showAST "(* Unit Unit)"
        `shouldBe` "Just (0 ** (1 * 1))"

    it "\"(+ Unit Void)\"" $ do
      showAST "(+ Unit Void)"
        `shouldBe` "Just (0 ** (1 + 0))"

    it "\"(+ Unit (* (var 0) Void))\"" $ do
      showAST "(+ Unit (* (var 0) Void))"
        `shouldBe` "Just (1 ** (1 + ({0} * 0)))"

    it "\"(+ Unit Unit Void)\"" $ do
      showAST "(+ Unit Unit Void)"
        `shouldBe` "Just (0 ** (1 + 1 + 0))"

    it "\"(+ Unit Unit Void (* Unit Void))\"" $ do
      showAST "(+ Unit Unit Void (* Unit Void))"
        `shouldBe` "Just (0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "ill-formed terms" $ do

    it "\"(*)\" - <2 operands" $ do
      showAST "(*)"
        `shouldBe` "Nothing"

    it "\"(+ Unit)\" - <2 operands" $ do
      showAST "(+ Unit)"
        `shouldBe` "Nothing"

    it "\"(mu list (nil Unit))\" - no free variables under mu" $ do
      showAST "(mu list (nil Unit))"
        `shouldBe` "Nothing"

    it "\"(+ Unit * Unit Void)\" - malformed" $ do
      showAST "(+ Unit * Unit Void)"
        `shouldBe` "Nothing"
