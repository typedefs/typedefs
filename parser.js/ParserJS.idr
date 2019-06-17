import Text.PrettyPrint.WL
import public Typedefs
import Parse
import public TermParse
import public TermWrite
import Backend
import Backend.Utils
import Backend.Haskell
import Backend.JSON
import Backend.ReasonML

generateCode : String -> (n ** TNamed n) -> String
generateCode "haskell"  (n  **tn) = toString $ generateDefs Haskell tn
generateCode _          _         = "<error : unsupported backend>"


generateTermSerializers : String -> String -> Maybe String
generateTermSerializers backend tdef = map (generateCode backend) (parseTNamed tdef)

generateType : String -> String -> Maybe String
generateType backend tdef = map (genType backend) (parseTNamed tdef)
  where
    genType : String -> (n ** TNamed n) -> String
    genType "reasonml" (n   ** tn) = toString $ generateDefs ReasonML tn
    genType "json"     (Z   ** tn) = toString $ generate JSONDef tn
    genType "json"     (S _ ** tn) = "<error : cannot generate JSON schema for open typedefs>"
    genType _          _           = "<error : unsupported backend>"

lib : FFI_Export FFI_JS "" []
lib = Data (Maybe String) "MaybeString" $
      Fun generateTermSerializers "generateTermSerializers" $
      Fun Main.generateType "generateType" $
      End
