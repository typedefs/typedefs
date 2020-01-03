module Typedefs.Test.IndexCompilerTests

import Typedefs.Typedefs
import Typedefs.Syntax.IndexFree
import Typedefs.Syntax.AST
import Typedefs.Syntax.Compiler

import TParsec
import TParsec.Running

import Data.NEList

import Typedefs.Equality
import Specdris.Spec

quote : String -> String
quote s = "\"" ++ s ++ "\""

compileExprShouldBe : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
compileExprShouldBe input exp =
  it (quote input) $ show
                  <$> (maybe (Left "Parse Error") Right (parseMaybeTopDef input)
                  >>= compileEither)
                  `shouldBe` (Right exp)

compileExprShouldFail : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
compileExprShouldFail input exp =
  it (quote input) $ (maybe (Left "Parse Error") Right (parseMaybeTopDef input) >>= compileEither)
  `shouldBe` (Left exp)

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
      "(1 ** (maybe := (mu [Empty: 1, Some: {1}])))"
    "List a := Nil : 1 | Cons : a * (List a)" `compileExprShouldBe`
      "(1 ** (List := (mu [Nil: 1, Cons: ({1} * {0})])))"
    "Nat := Z : 1 | S : Nat" `compileExprShouldBe` "(0 ** (Nat := (mu [Z: 1, S: {0}])))"
    "Either a b := a + b" `compileExprShouldBe` "(2 ** (Either := ({0} + {1})))"
    "Wrong a b c := Base : 1 | Rec : a + (Wrong b c)" `compileExprShouldFail`
      "Type \"Wrong\" expected 3 arguments, got 2"
--     (name either (+ (var 0) (var 1)))
--     (name bit (+ 1 1))
--     (name nibble (* bit bit bit bit))
--     (name bitOrNibble (either bit nibble))

