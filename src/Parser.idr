import AST
import TParse

import TParsec
import TParsec.Running

parseTDef : String -> String
parseTDef str = do
  show $ parseMaybe str tdefAst

main : IO ()
main = do
  [_, str] <- getArgs
  putStrLn $ parseTDef str
