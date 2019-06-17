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

-- re-exports
parseType : String -> Maybe (n : Nat ** TNamed n)
parseType = parseTNamed 

generateSerializers : String -> String -> Maybe String
generateSerializers backend tdef = map (generateCode backend) (parseType tdef)

genType : String -> (n ** TNamed n) -> String
genType "reasonml" (n   ** tn) = toString $ generateDefs ReasonML tn
genType "json"     (Z   ** tn) = toString $ generate JSONDef tn
genType "json"     (S _ ** tn) = "<error : cannot generate JSON schema for open typedefs>"
genType _          _           = "<error : unsupported backend>"

generateTypeSignature : String -> String -> Maybe String
generateTypeSignature backend tdef = map (genType backend) (parseType tdef)

lib : FFI_Export FFI_JS "" []
lib = Data (Maybe String) "MaybeString" $
      Fun generateSerializers "generateSerializers" $
      Fun generateTypeSignature "generateTypeSignature" $
      End
