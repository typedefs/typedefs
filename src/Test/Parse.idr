module Test.Parse

import TParsec
import TParsec.Running

import Typedefs
import Parse

import Specdris.Spec

%access public export

itShouldParseAs : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
itShouldParseAs input exp = it (quote input) $ (parseThenShowTDef input) `shouldBe` exp
  where
    quote : String -> String
    quote s = "\"" ++ s ++ "\""

testSuite : IO ()
testSuite = spec $ do

  describe "Parser tests: well-formed terms" $ do
    "0" `itShouldParseAs` "Just (0 ** 0)"

    "1" `itShouldParseAs` "Just (0 ** 1)"

    "(var 123)" `itShouldParseAs` "Just (124 ** {123})"

    "(var 0)" `itShouldParseAs` "Just (1 ** {0})"

    "(var 0) " `itShouldParseAs` "Just (1 ** {0})"

    "(name maybe (+ 1 (var 0)))" `itShouldParseAs` "Just (1 ** maybe [(1 + {0})])"

    "(mu list (cons (* (var 1) (var 0))))" `itShouldParseAs` "Just (1 ** list = mu [cons: ({1} * {0})])"

    "(mu list (nil 1) (cons (* (var 1) (var 0))))" `itShouldParseAs` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    "(mu list (nil 1) (cons (* (var 1) (var 0)) ))" `itShouldParseAs` "Just (1 ** list = mu [nil: 1, cons: ({1} * {0})])"

    "(* 1 1)" `itShouldParseAs` "Just (0 ** (1 * 1))"

    "(+ 1 0)" `itShouldParseAs` "Just (0 ** (1 + 0))"

    "(+ 1 (* (var 0) 0))" `itShouldParseAs` "Just (1 ** (1 + ({0} * 0)))"

    "(+ 1 1 0)" `itShouldParseAs` "Just (0 ** (1 + 1 + 0))"

    "(+ 1 1 0 (* 1 0))" `itShouldParseAs` "Just (0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "Parser tests: ill-formed terms" $ do

    "(*)" `itShouldParseAs` "Nothing"

    "(+ 1)" `itShouldParseAs` "Nothing"

    "(mu list (nil 1))" `itShouldParseAs` "Nothing"

    "(+ 1 * 1 0)" `itShouldParseAs` "Nothing"
