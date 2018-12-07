import Typedefs
import Parse
import Backend.Utils
import Backend.Haskell

getSource : JS_IO String
getSource = foreign FFI_JS "getSource()" _

setResult : String -> JS_IO ()
setResult = foreign FFI_JS "setResult(%0)" _

main : JS_IO ()
main = setResult $ parseThenStrFun !getSource (\td => print . generate {lang=Haskell} $ DPair.snd td)