import public Typedefs
import Parse
import public TermParse
import public TermWrite
import Backend
import Backend.Utils
import Backend.Haskell
import Backend.JSON
import Backend.ReasonML

getSource : JS_IO String
getSource = foreign FFI_JS "getSource()" _

setResult : String -> JS_IO ()
setResult = foreign FFI_JS "setResult(%0)" _

-- re-exports
parseType : String -> Maybe (n : Nat ** TNamed n)
parseType = parseTNamed

generateHaskell : TNamed n -> Doc
generateHaskell = generateDefs Haskell

generateReason : TNamed n -> Doc
generateReason = generateDefs ReasonML

generateJSON : TNamed 0 -> Doc
generateJSON = generate JSONDef
