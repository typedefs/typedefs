import TParsec
import TParsec.Running

import Typedefs
import TParseTDef

showTDef : String -> String
showTDef str = do
  show $ parseMaybe str tdef

getSource : JS_IO String
getSource = foreign FFI_JS "getSource()" _

setResult : String -> JS_IO ()
setResult = foreign FFI_JS "setResult(%0)" _

main : JS_IO ()
main = do
  setResult $ showTDef !getSource
