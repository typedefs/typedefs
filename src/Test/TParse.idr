module Test.TParse

import TParsec
import TParsec.Running

import AST as AST
import TParse

%access public export

-- TODO render errors

testParseAST : String -> IO ()
testParseAST str = do putStrLn $ "'" ++ str ++ "'"
                      putStrLn . show $ TParse.parseMaybe str tdefAst
                      putStrLn ""

testSuite : IO ()
testSuite = do

  putStrLn "-- well-formed terms -----------------------------------------------------------"
  putStrLn ""
  testParseAST "Void"
  testParseAST "Unit"
  testParseAST "(var 123)"
  testParseAST "(var 0)"
  testParseAST "(mu list (nil Unit))"
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
