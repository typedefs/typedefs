import AST
import TParse

import TParsec
import TParsec.Running

parseTDef : String -> String
parseTDef str = do
  show $ parseMaybe str tdefAst

getSource : JS_IO String
getSource = foreign FFI_JS "getSource()" _


setResult : String -> JS_IO ()
setResult = foreign FFI_JS "setResult(%0)" _

main : JS_IO ()
main = do
  setResult $ parseTDef !getSource
