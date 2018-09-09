module Test.TParse

import TParsec
import TParsec.Running

import AST as AST
import TParse

import Specdris.Spec

%access public export

showAST : String -> String
showAST str = do
  show $ parseMaybe str tdefAst

testSuite : IO ()
testSuite = spec $ do

  describe "well-formed terms" $ do

    it "\"Void\"" $ do
      showAST "Void"
        `shouldBe` "Just Void"

    it "\"Unit\"" $ do
      showAST "Unit"
        `shouldBe` "Just Unit"

    it "\"(var 123)\"" $ do
      showAST "(var 123)"
        `shouldBe` "Just (Var 123)"

    it "\"(var 0)\"" $ do
      showAST "(var 0)"
        `shouldBe` "Just (Var 0)"

    it "\"(var 0) \"" $ do
      showAST "(var 0) "
        `shouldBe` "Just (Var 0)"

    it "\"(mu list (nil Unit))\"" $ do
      showAST "(mu list (nil Unit))"
        `shouldBe` "Just (Mu \"list\" [Unit])"

    it "\"(mu list (cons (* (var 1) (var 0))))\"" $ do
      showAST "(mu list (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (Mu \"list\" [(Prod (Var 1) (Var 0))])"

    it "\"(mu list (nil Unit) (cons (* (var 1) (var 0))))\"" $ do
      showAST "(mu list (nil Unit) (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (Mu \"list\" [Unit, (Prod (Var 1) (Var 0))])"

    it "\"(mu list (nil Unit) (cons (* (var 1) (var 0)) ))\"" $ do
      showAST "(mu list (nil Unit) (cons (* (var 1) (var 0)) ))"
        `shouldBe` "Just (Mu \"list\" [Unit, (Prod (Var 1) (Var 0))])"

    it "\"(* Unit Unit)\"" $ do
      showAST "(* Unit Unit)"
        `shouldBe` "Just (Prod Unit Unit)"

    it "\"(+ Unit Void)\"" $ do
      showAST "(+ Unit Void)"
        `shouldBe` "Just (Sum Unit Void)"

    it "\"(+ Unit (* (var 0) Void))\"" $ do
      showAST "(+ Unit (* (var 0) Void))"
        `shouldBe` "Just (Sum Unit (Prod (Var 0) Void))"

    it "\"(+ Unit Unit Void)\"" $ do
      showAST "(+ Unit Unit Void)"
        `shouldBe` "Just (Sum Unit Unit Void)"

    it "\"(+ Unit Unit Void (* Unit Void))\"" $ do
      showAST "(+ Unit Unit Void (* Unit Void))"
        `shouldBe` "Just (Sum Unit Unit Void (Prod Unit Void))"

  describe "ill-formed terms" $ do

    it "\"(*)\"" $ do
      showAST "(*)"
        `shouldBe` "Nothing"

    it "\"(+ Unit)\"" $ do
      showAST "(+ Unit)"
        `shouldBe` "Nothing"

    it "\"(+ Unit * Unit Void)\"" $ do
      showAST "(+ Unit * Unit Void)"
        `shouldBe` "Nothing"
