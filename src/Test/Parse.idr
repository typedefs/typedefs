module Test.Parse

import Parse

import Text.Parser
import Lex as Lex
import Token as Tok
import AST as AST
import Typedefs as Typedefs

%access public

export
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

  testParseAST : String -> IO ()
  testParseAST str = (do
    putStrLn . show $ map text          <$> tokens
    putStrLn . show $ map (show . kind) <$> tokens
    putStrLn . show $ astify str
    putStrLn ""
    )
    where
      tokens : Maybe (List TypeToken)
      tokens = filter (not . Lex.isTDWhitespace) <$> Lex.typedef str

  testSuite : IO ()
  testSuite = do

    putStrLn "-- well-formed terms -----------------------------------------------------------"
    putStrLn ""
    testParseAST "Void"
    testParseAST "Unit"
    testParseAST "(mu list Unit)"
    testParseAST "(mu list (* Unit Unit))"
    testParseAST "(* Unit Unit)"
    testParseAST "(+ Unit Void)"
    testParseAST "(+ Unit (* Unit Void))"

    putStrLn "-- ill-formed terms ------------------------------------------------------------"
    putStrLn ""
    testParseAST "(+ Unit * Unit Void)"
    testParseAST "(+ Unit Unit Void)"
