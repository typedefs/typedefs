module Typedefs.Test.IndexFree

import Typedefs.Typedefs
import Typedefs.Syntax.IndexFree
import Typedefs.Syntax.AST

import TParsec
import TParsec.Running

import Data.NEList

import Specdris.Spec

Traversable NEList where
  traverse f (MkNEList x xs) = [| MkNEList (f x) (traverse f xs) |]

quote : String -> String
quote s = "\"" ++ s ++ "\""

tdefShouldParseAs : String -> String -> Tree (Either SpecInfo (IO' ffi SpecResult))
tdefShouldParseAs input exp = it (quote input) $ (show <$> parseMaybeExpr input) `shouldBe` Just exp

tdefProgramShouldParseAs : String -> List String -> Tree (Either SpecInfo (IO' ffi SpecResult))
tdefProgramShouldParseAs input exp = it (quote input) $ (map show <$> NEList.toList <$> parseDefList input) `shouldBe` Just exp

testSuite : IO ()
testSuite = spec $ do

--   describe "Parser tests: comments" $ do
--
--     "0;comment\n" `tdefShouldParseAs` Value "(0 ** 0)"
--
--     "0;\n" `tdefShouldParseAs` Value "(0 ** 0)"
--
--     "; first line\n; second line\n(+ 1 1)" `tdefShouldParseAs` Value "(0 ** (1 + 1))"
--
--     "; comment followed by empty\n\n(+ 1 1)" `tdefShouldParseAs` Value "(0 ** (1 + 1))"
--
--     "(var ;comment\n123)" `tdefShouldParseAs` Value "(124 ** {123})"

  describe "Parser tests: well-formed expressions" $ do
    "0" `tdefShouldParseAs` "0"

    "1" `tdefShouldParseAs` "1"

    "a" `tdefShouldParseAs` "a"

    "1 * 1" `tdefShouldParseAs` "1 * 1"

    "1 + 0" `tdefShouldParseAs` "1 + 0"

    "1 + a * 0" `tdefShouldParseAs` "1 + a * 0"

    "1 + 1 + 0" `tdefShouldParseAs` "1 + 1 + 0"

    "1 + 1 + 0 + 1 * 0" `tdefShouldParseAs` "1 + 1 + 0 + 1 * 0"

--   describe "Parser tests: ill-formed terms" $ do
--
--     "(*)" `tdefShouldParseAs` (HardFail $ ParseError $ MkPosition 0 2)
--
--     "(+ 1)" `tdefShouldParseAs` (HardFail $ ParseError $ MkPosition 0 4)
--
--     "(mu list (nil 1))" `tdefShouldParseAs` (HardFail $ ParseError $ MkPosition 0 5)
--
--     "(+ 1 * 1 0)" `tdefShouldParseAs` (HardFail $ ParseError $ MkPosition 0 5)
--
--     "(mu nat (Z 1) (S (var 0))) (name mpat (+ 1 pat))" `tdefShouldParseAs` (HardFail $ ParseError $ MkPosition 0 5)
--
--     "(name maybe (+ 1 (var 0)))" `tdefShouldParseAs` (SoftFail $ ParseError $ MkPosition 0 0)
--
--     "(mu list (cons (* (var 1) (var 0))))" `tdefShouldParseAs` (HardFail $ ParseError $ MkPosition 0 5)

  describe "Parser tests: well-formed definitions" $ do
    "Maybe a := 1+a" `tdefProgramShouldParseAs` ["Maybe a := 1 + a"]

    "Nat := Z : 1 | S : Nat" `tdefProgramShouldParseAs` ["Nat := Z : 1 | S : Nat"]

    """Nat := Z : 1 | S : Nat
       ListNat := Nil : 1 | Cons : Nat * ListNat"""
      `tdefProgramShouldParseAs`
       [ "Nat := Z : 1 | S : Nat"
       , "ListNat := Nil : 1 | Cons : Nat * ListNat"]

    "bitOrNibble := bit + nibble"
      `tdefProgramShouldParseAs`
        ["bitOrNibble := bit + nibble"]

--   describe "Parser tests: ill-formed definitions" $ do
--     "(mu nat (Z 1) (S (var 0))) (name mnat (+ 1 nat)) (mu listmnat (nil 1) (cons (* mnat (var 0))))"
--       `tdefProgramShouldParseAs`
--         (SoftFail $ ParseError $ MkPosition 0 2)
--
--     "0" `tdefProgramShouldParseAs` (SoftFail $ ParseError $ MkPosition 0 1)
