module Test.Parse

import Text.Parser

import AST as AST
import Typedefs as Typedefs
import Parse
import Parse.Lex as Lex
import Parse.Token as Tok

import Specdris.Spec

%access public export

-- TODO render errors
parseTypedef : List TypeToken -> Maybe AST.TDef
parseTypedef toks =
  case parse typedef (filter (not . Lex.isTDWhitespace) toks) of
       Right (t, []) => Just t
       _             => Nothing

astify : String -> Maybe AST.TDef
astify str = do
  tokens <- Lex.typedef str
  parseTypedef tokens

showAST : String -> String
showAST str = do
  show $ astify str

testParseAST : String -> IO ()
testParseAST str = do printLn $ map Token.text    <$> tokens
                      printLn $ map (show . kind) <$> tokens
                      printLn $ astify str
                      putStrLn ""
  where
  tokens : Maybe (List TypeToken)
  tokens = filter (not . Lex.isTDWhitespace) <$> Lex.typedef str


testSuite : IO ()
testSuite = spec $ do

  describe "well-formed terms" $ do

    it "Void" $ do
      showAST "Void"
        `shouldBe` "Just Void"

    it "Unit" $ do
      showAST "Unit"
        `shouldBe` "Just Unit"

    it "(var 123)" $ do
      showAST "(var 123)"
        `shouldBe` "Just (Var 123)"

    it "(var 0) " $ do
      showAST "(var 0) "
        `shouldBe` "Just (Var 0)"

    it "(mu list Unit)" $ do
      showAST "(mu list Unit)"
        `shouldBe` "Just (Mu \"list\" [Unit])"

    it "(mu list (* Unit Unit))" $ do
      showAST "(mu list (* Unit Unit))"
        `shouldBe` "Just (Mu \"list\" [(Prod Unit Unit)])"

    it "(mu list (cons (* (var 1) (var 0))))" $ do
      showAST "(mu list (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (Mu \"list\" [(Prod (Var 1) (Var 0))])"

    it "(mu list (nil Unit) (cons (* (var 1) (var 0))))" $ do
      showAST "(mu list (nil Unit) (cons (* (var 1) (var 0))))"
        `shouldBe` "Just (Mu \"list\" [Unit, (Prod (Var 1) (Var 0))])"

    it "(* Unit Unit)" $ do
      showAST "(* Unit Unit)"
        `shouldBe` "Just (Prod Unit Unit)"

    it "(+ Unit Void)" $ do
      showAST "(+ Unit Void)"
        `shouldBe` "Just (Sum Unit Void)"

    it "(+ Unit (* (var 0) Void))" $ do
      showAST "(+ Unit (* (var 0) Void))"
        `shouldBe` "Just (Sum Unit (Prod (Var 0) Void))"

    it "(+ Unit Unit Void)" $ do
      showAST "(+ Unit Unit Void)"
        `shouldBe` "Just (Sum Unit Unit Void)"

    it "(+ Unit Unit Void (* Unit Void))" $ do
      showAST "(+ Unit Unit Void (* Unit Void))"
        `shouldBe` "Just (Sum Unit Unit Void (Prod Unit Void))"

  describe "ill-formed terms" $ do

    it "(*)" $ do
      showAST "(*)"
        `shouldBe` "Nothing"

    it "(+ Unit)" $ do
      showAST "(+ Unit)"
        `shouldBe` "Nothing"

    it "(+ Unit * Unit Void)" $ do
      showAST "(+ Unit * Unit Void)"
        `shouldBe` "Nothing"

testTokens : IO ()
testTokens = do

  putStrLn "-- well-formed terms -----------------------------------------------------------"
  putStrLn ""

  testParseAST "Void"
  testParseAST "Unit"
  testParseAST "(var 123)"
  testParseAST "(var 0)"
  testParseAST "(mu list Unit)"
  testParseAST "(mu list (* Unit Unit))"
  testParseAST "(mu list (cons (* (var 1) (var 0))))"
  testParseAST "(mu list (nil Unit) (cons (* (var 1) (var 0))))"
  testParseAST "(* Unit Unit)"
  testParseAST "(+ Unit Void)"
  testParseAST "(+ Unit (* (var 0) Void))"
  testParseAST "(+ Unit Unit Void)"
  testParseAST "(+ Unit Unit Void (* Unit Void))"

  putStrLn "-- ill-formed terms ------------------------------------------------------------"
  putStrLn ""

  testParseAST "(*)"
  testParseAST "(+ Unit)"
  testParseAST "(+ Unit * Unit Void)"
