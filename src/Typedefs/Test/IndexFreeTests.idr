module Typedefs.Test.IndexFreeTests

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

export
testSuite : IO ()
testSuite = spec $ do

  describe "Parser tests: well-formed expressions" $ do
    "0" `tdefShouldParseAs` "0"

    "1" `tdefShouldParseAs` "1"

    "a" `tdefShouldParseAs` "a"

    "1 * 1" `tdefShouldParseAs` "1 * 1"

    "1 + 0" `tdefShouldParseAs` "1 + 0"

    "1 + a * 0" `tdefShouldParseAs` "1 + a * 0"

    "1 + 1 + 0" `tdefShouldParseAs` "1 + 1 + 0"

    "1 + 1 + 0 + 1 * 0" `tdefShouldParseAs` "1 + 1 + 0 + 1 * 0"

    "list a" `tdefShouldParseAs` "list a"

    "list 1" `tdefShouldParseAs` "list 1"


  describe "Parser tests: well-formed definitions" $ do
    "Maybe a := 1+a" `tdefProgramShouldParseAs` ["Maybe a := 1 + a"]

    "Nat := Z : 1 | S : Nat" `tdefProgramShouldParseAs` ["Nat := Z : 1 | S : Nat"]

    "List a := Nil : 1 | Cons : a * List a" `tdefProgramShouldParseAs`
      ["List a := Nil : 1 | Cons : a * List a"]
    """Nat := Z : 1 | S : Nat
       ListNat := Nil : 1 | Cons : Nat * ListNat"""
      `tdefProgramShouldParseAs`
       [ "Nat := Z : 1 | S : Nat"
       , "ListNat := Nil : 1 | Cons : Nat * ListNat"]

    "bitOrNibble := bit + nibble"
      `tdefProgramShouldParseAs`
        ["bitOrNibble := bit + nibble"]

--    "List a := Nil : 1 | Cons : a + List a"
--      `tdefProgramShouldParseAs`
--        ["List a := Nil : 1 | Cons : a + List a"]

--   describe "Parser tests: ill-formed definitions" $ do
--     "(mu nat (Z 1) (S (var 0))) (name mnat (+ 1 nat)) (mu listmnat (nil 1) (cons (* mnat (var 0))))"
--       `tdefProgramShouldParseAs`
--         (SoftFail $ ParseError $ MkPosition 0 2)
--
--     "0" `tdefProgramShouldParseAs` (SoftFail $ ParseError $ MkPosition 0 1)
