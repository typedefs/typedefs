module Test.ParseTests

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

  describe "Parser tests: comments" $ do

    "0;comment\n" `tdefShouldParseAs` "(0 ** 0)"

    "0;\n" `tdefShouldParseAs` "(0 ** 0)"

    "; first line\n; second line\n(+ 1 1)" `tdefShouldParseAs` "(0 ** (1 + 1))"

    "; comment followed by empty\n\n(+ 1 1)" `tdefShouldParseAs` "(0 ** (1 + 1))"

    "(var ;comment\n123)" `tdefShouldParseAs` "(124 ** {123})"

  describe "Parser tests: well-formed terms" $ do
    "0" `tdefShouldParseAs` "(0 ** 0)"

    "1" `tdefShouldParseAs` "(0 ** 1)"

    "(var 123)" `tdefShouldParseAs` "(124 ** {123})"

    "(var 0)" `tdefShouldParseAs` "(1 ** {0})"

    "(var 0) " `tdefShouldParseAs` "(1 ** {0})"

    "(mu (cons (* (var 1) (var 0))))" `tdefShouldParseAs` "(1 ** (mu [cons: ({1} * {0})]))"

    "(mu (nil 1) (cons (* (var 1) (var 0))))" `tdefShouldParseAs` "(1 ** (mu [nil: 1, cons: ({1} * {0})]))"

    "(mu (nil 1) (cons (* (var 1) (var 0)) ))" `tdefShouldParseAs` "(1 ** (mu [nil: 1, cons: ({1} * {0})]))"

    "(* 1 1)" `tdefShouldParseAs` "(0 ** (1 * 1))"

    "(+ 1 0)" `tdefShouldParseAs` "(0 ** (1 + 0))"

    "(+ 1 (* (var 0) 0))" `tdefShouldParseAs` "(1 ** (1 + ({0} * 0)))"

    "(+ 1 1 0)" `tdefShouldParseAs` "(0 ** (1 + 1 + 0))"

    "(+ 1 1 0 (* 1 0))" `tdefShouldParseAs` "(0 ** (1 + 1 + 0 + (1 * 0)))"

  describe "Parser tests: ill-formed terms" $ do

    "(*)" `tdefShouldParseAs` "hard fail: parse error: 0:2"

    "(+ 1)" `tdefShouldParseAs` "hard fail: parse error: 0:4"

    "(mu list (nil 1))" `tdefShouldParseAs` "hard fail: parse error: 0:5"

    "(+ 1 * 1 0)" `tdefShouldParseAs` "hard fail: parse error: 0:5"

    "(mu nat (Z 1) (S (var 0))) (name mpat (+ 1 pat))" `tdefShouldParseAs` "hard fail: parse error: 0:5"

    "(name maybe (+ 1 (var 0)))" `tdefShouldParseAs` "soft fail: parse error: 0:0"

    "(mu list (cons (* (var 1) (var 0))))" `tdefShouldParseAs` "hard fail: parse error: 0:5"

  describe "Parser tests: well-formed definitions" $ do
    "(name maybe (+ 1 (var 0)))" `tnamedShouldParseAs` "(1 ** (maybe := (1 + {0})))"

    "(name nat (mu (Z 1) (S (var 0))))" `tnamedShouldParseAs` "(0 ** (nat := (mu [Z: 1, S: {0}])))"

    "(name nat (mu (Z 1) (S (var 0)))) (name mnat (+ 1 nat)) (name listmnat (mu (nil 1) (cons (* mnat (var 0)))))"
      `tnamedShouldParseAs`
        "(0 ** (listmnat := (mu [nil: 1, cons: (mnat * {0})])))"

    """
    (name either (+ (var 0) (var 1)))
    (name bit (+ 1 1))
    (name nibble (* bit bit bit bit))
    (name bitOrNibble (either bit nibble))
    """ 
      `tnamedShouldParseAs`
        "(0 ** (bitOrNibble := (either bit nibble)))"

  describe "Parser tests: ill-formed definitions" $ do
    "(mu nat (Z 1) (S (var 0))) (name mnat (+ 1 nat)) (mu listmnat (nil 1) (cons (* mnat (var 0))))"
      `tnamedShouldParseAs`
        "soft fail: parse error: 0:2"

    "0" `tnamedShouldParseAs` "soft fail: parse error: 0:1"
