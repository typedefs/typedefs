module Test.Parse

import TParsec
import TParsec.Running

import Typedefs
import Parse

import Specdris.Spec

%access public export

testSuite : IO ()
testSuite = spec $ do

  describe "Parser tests: well-formed terms" $ do

    it "\"0\"" $ 
      showTDef "0"
        `shouldBe` "Just (0 ** 0)"

    it "\"1\"" $ 
      showTDef "1"
        `shouldBe` "Just (0 ** 1)"

    it "\"(var 123)\"" $ 
      showTDef "(var 123)"
        `shouldBe` "Just (124 ** {123})"

    it "\"(var 0)\"" $ 
      showTDef "(var 0)"
        `shouldBe` "Just (1 ** {0})"

    it "\"(var 0) \"" $ 
      showTDef "(var 0) "
        `shouldBe` "Just (1 ** {0})"

    it "\"(name maybe (+ 1 (var 0)))\"" $
      showTDef "(name maybe (+ 1 (var 0)))"
        `shouldBe` "Just (1 ** maybe[(1 + {0})])"

    it "\"(mu list (cons (* (var 1) (var 0))))\"" $ 
      showTDef "(mu list (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [cons: ({1} * {0})])"

    it "\"(mu list (nil 1) (cons (* (var 1) (var 0))))\"" $ 
      showTDef "(mu list (nil 1) (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(mu list (nil 1) (cons (* (var 1) (var 0)) ))\"" $ 
      showTDef "(mu list (nil 1) (cons (* (var 1) (var 0)) ))"
        `shouldBe` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    it "\"(* 1 1)\"" $ 
      showTDef "(* 1 1)"
        `shouldBe` "Just (0 ** (1 * 1))"

    it "\"(+ 1 0)\"" $ 
      showTDef "(+ 1 0)"
        `shouldBe` "Just (0 ** (1 + 0))"

    it "\"(+ 1 (* (var 0) 0))\"" $ 
      showTDef "(+ 1 (* (var 0) 0))"
        `shouldBe` "Just (1 ** (1 + ({0} * 0)))"

    it "\"(+ 1 1 0)\"" $ 
      showTDef "(+ 1 1 0)"
        `shouldBe` "Just (0 ** (1 + 1 + 0))"

    it "\"(+ 1 1 0 (* 1 0))\"" $ 
      showTDef "(+ 1 1 0 (* 1 0))"
        `shouldBe` "Just (0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "Parser tests: ill-formed terms" $ do

    it "\"(*)\" - <2 operands" $ 
      showTDef "(*)"
        `shouldBe` "Nothing"

    it "\"(+ 1)\" - <2 operands" $ 
      showTDef "(+ 1)"
        `shouldBe` "Nothing"

    it "\"(mu list (nil 1))\" - no free variables under mu" $ 
      showTDef "(mu list (nil 1))"
        `shouldBe` "Nothing"

    it "\"(+ 1 * 1 0)\" - malformed" $ 
      showTDef "(+ 1 * 1 0)"
        `shouldBe` "Nothing"
