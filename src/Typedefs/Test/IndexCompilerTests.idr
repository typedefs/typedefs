module Typedefs.Test.IndexCompilerTests

import Typedefs.Typedefs
import Typedefs.Syntax.IndexFree
import Typedefs.Syntax.AST
import Typedefs.Syntax.Compiler

import TParsec
import TParsec.Running

import Data.NEList

import Specdris.Spec

quote : String -> String
quote s = "\"" ++ s ++ "\""

compileExprShouldBe : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
compileExprShouldBe input exp =
  it (quote input) $ ((map show)
                  <$> compileEither
                  <$> parseMaybeTopDef input)
                  `shouldBe` Just (Right exp)

compileProgramShouldBe : String -> List String -> Tree (Either SpecInfo (IO' ffi SpecResult))
compileProgramShouldBe input exp =
  it (quote input) $ (traverse (\x => show <$> compileEither x)
                  <$> NEList.toList
                  <$> parseDefList input)
                  `shouldBe` Just (Right exp)

testSuite : IO ()
testSuite = spec $ do
  describe "Single defintion compiler" $ do
    "Binary := 1 + 1" `compileExprShouldBe` "(0 ** (Binary := (1 + 1)))"
    "maybe a := 1 + a" `compileExprShouldBe` "(1 ** (maybe := (1 + {0})))"
    "maybe a := Empty : 1 | Some : a" `compileExprShouldBe`
      "(1 ** (maybe := (mu [Empty: 1, Some: {0}]))"
    "List a := Nil : 1 | Cons : a + List a" `compileExprShouldBe`
      "(1 ** (List := (mu [Nil: 1, Cons: ({1} + {0})])))"
