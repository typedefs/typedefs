module Typedefs.Test.IndexFreeTests

import Typedefs.Typedefs
import Typedefs.Syntax.IndexFree
import Typedefs.Syntax.AST

import TParsec
import TParsec.Running

import Data.NEList

import Specdris.Spec

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

    it "list a + 3" $ (parseMaybeExpr "list a + 3") `shouldBe`
      (Just (ESum (EEmb $ TEmb $ FEmb $ App (AEmb $ PRef "list")
                                           (PRef "a"))
                 (TEmb $ FEmb $ AEmb $ PLit 3)))

    it "list a b + 3" $ (parseMaybeExpr "list a b + 3") `shouldBe`
     (Just (ESum (EEmb $ TEmb $ FEmb $ App (App (AEmb $ PRef "list")
                                           (PRef "a")) (PRef "b"))
                (TEmb $ FEmb $ AEmb $ PLit 3)))


  describe "Parser tests: well-formed definitions" $ do
    "Maybe a := 1+a;" `tdefProgramShouldParseAs` ["Maybe a := 1 + a"]

    "Nat := Z : 1 | S : Nat;" `tdefProgramShouldParseAs` ["Nat := Z : 1 | S : Nat"]

    "List a := Nil : 1 | Cons : a * List a;" `tdefProgramShouldParseAs`
      ["List a := Nil : 1 | Cons : a * List a"]
    ("Nat := Z : 1 | S : Nat;\n" ++
      "ListNat := Nil : 1 | Cons : Nat * ListNat;")
      `tdefProgramShouldParseAs`
       [ "Nat := Z : 1 | S : Nat"
       , "ListNat := Nil : 1 | Cons : Nat * ListNat"]

    "bitOrNibble := bit + nibble;"
      `tdefProgramShouldParseAs`
        ["bitOrNibble := bit + nibble"]
    it "BinaryTree a b := Left : a | Right : b | Node : (a + b) * BinaryTree a b;" $
       (parseDefList "BinaryTree a b := Left : a | Right : b | Node : (a + b) * BinaryTree a b;")
         `shouldBe`
           Just (MkNEList (MkTopLevelDef (MkDefName "BinaryTree" ["a", "b"])
             (Enum [ ("Left", EEmb $ TEmb $ FEmb $ AEmb $ PRef "a")
                   , ("Right", EEmb $ TEmb $ FEmb $ AEmb $ PRef "b")
                   , ("Node", EEmb $ TMul (TEmb $ FEmb $ AEmb $ PEmb $ ESum
                                                 (EEmb $ TEmb $ FEmb $ AEmb $ PRef "a")
                                                 (TEmb $ FEmb $ AEmb $ PRef "b"))
                                          (FEmb $ App (App (AEmb $ PRef "BinaryTree")
                                                           (PRef "a"))
                                                      (PRef "b")))
                   ])) [])


