module Test.TParse

import TParsec
import TParsec.Running

import AST as AST
import TParse

%access public export

-- TODO render errors

testParseAST : String -> IO ()
testParseAST str = do putStrLn $ "'" ++ str ++ "'"
                      putStrLn . show $ parseMaybe str tdefAst
                      putStrLn ""

testSuite : IO ()
testSuite = do

  putStrLn "-- well-formed terms -----------------------------------------------------------"
  putStrLn ""
  testParseAST "Void"
  testParseAST "Unit"
  testParseAST "(var 123)"
  testParseAST "(var 0)"
  testParseAST "(mu list Unit)"
  testParseAST "(mu list (* Unit Unit))"
  testParseAST "(* Unit Unit)"
  testParseAST "(+ Unit Void)"
  testParseAST "(+ Unit (* (var 0) Void))"

  putStrLn "-- ill-formed terms ------------------------------------------------------------"
  putStrLn ""
  testParseAST "(+ Unit * Unit Void)"
  testParseAST "(+ Unit Unit Void)"
