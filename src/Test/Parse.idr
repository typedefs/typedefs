module Test.Parse

import TParsec
import TParsec.Running

import Typedefs
import Parse

import Specdris.Spec

%access public export

quote : String -> String
quote s = "\"" ++ s ++ "\""

tdefShouldParseAs : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
tdefShouldParseAs input exp = it (quote input) $ (parseThenShowTDef input) `shouldBe` exp

tnamedShouldParseAs : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
tnamedShouldParseAs input exp = it (quote input) $ (parseThenShowTNamed input) `shouldBe` exp

testSuite : IO ()
testSuite = spec $ do

  describe "Parser tests: well-formed terms" $ do
    "0" `tdefShouldParseAs` "Just (0 ** 0)"

    "1" `tdefShouldParseAs` "Just (0 ** 1)"

    "(var 123)" `tdefShouldParseAs` "Just (124 ** {123})"

    "(var 0)" `tdefShouldParseAs` "Just (1 ** {0})"

    "(var 0) " `tdefShouldParseAs` "Just (1 ** {0})"

    "(mu (cons (* (var 1) (var 0))))" `tdefShouldParseAs` "Just (1 ** (mu [cons: ({1} * {0})]))"

    "(mu (nil 1) (cons (* (var 1) (var 0))))" `tdefShouldParseAs` "Just (1 ** (mu [nil: 1, cons: ({1} * {0})]))"

    "(mu (nil 1) (cons (* (var 1) (var 0)) ))" `tdefShouldParseAs` "Just (1 ** (mu [nil: 1, cons: ({1} * {0})]))"

    "(* 1 1)" `tdefShouldParseAs` "Just (0 ** (1 * 1))"

    "(+ 1 0)" `tdefShouldParseAs` "Just (0 ** (1 + 0))"

    "(+ 1 (* (var 0) 0))" `tdefShouldParseAs` "Just (1 ** (1 + ({0} * 0)))"

    "(+ 1 1 0)" `tdefShouldParseAs` "Just (0 ** (1 + 1 + 0))"

    "(+ 1 1 0 (* 1 0))" `tdefShouldParseAs` "Just (0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "Parser tests: ill-formed terms" $ do

    "(*)" `tdefShouldParseAs` "Nothing"

    "(+ 1)" `tdefShouldParseAs` "Nothing"

    "(mu list (nil 1))" `tdefShouldParseAs` "Nothing"

    "(+ 1 * 1 0)" `tdefShouldParseAs` "Nothing"

    "(mu nat (Z 1) (S (var 0))) (name mpat (+ 1 pat))" `tdefShouldParseAs` "Nothing"

    "(name maybe (+ 1 (var 0)))" `tdefShouldParseAs` "Nothing"

    "(mu list (cons (* (var 1) (var 0))))" `tdefShouldParseAs` "Nothing"

  describe "Parser tests: well-formed definitions" $ do
    "(name maybe (+ 1 (var 0)))" `tnamedShouldParseAs` "Just (1 ** (maybe := (1 + {0})))"

    "(name nat (mu (Z 1) (S (var 0))))" `tnamedShouldParseAs` "Just (0 ** (nat := (mu [Z: 1, S: {0}])))"

    "(name nat (mu (Z 1) (S (var 0)))) (name mnat (+ 1 nat)) (name listmnat (mu (nil 1) (cons (* mnat (var 0)))))"
      `tnamedShouldParseAs`
        "Just (0 ** (listmnat := (mu [nil: 1, cons: (mnat * {0})])))"

  describe "Parser tests: ill-formed definitions" $ do
    "(mu nat (Z 1) (S (var 0))) (name mnat (+ 1 nat)) (mu listmnat (nil 1) (cons (* mnat (var 0))))"
      `tnamedShouldParseAs`
        "Nothing"

    "0" `tnamedShouldParseAs` "Nothing"
