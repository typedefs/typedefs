import TParsec
import TParsec.Running

import Typedefs
import TParseTDef

showTDef : String -> String
showTDef str = do
  show $ parseMaybe str tdef

main : IO ()
main = do
  [_, str] <- getArgs
  putStrLn $ showTDef str
