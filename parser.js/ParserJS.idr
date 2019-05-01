import Data.Vect
import Data.Vect.Quantifiers

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
generateCode "reasonml" (n  **tn) = toString $ generateDefs ReasonML tn
generateCode "json"     (Z  **tn) = toString $ generate JSONDef tn
generateCode "json"     (S _**tn) = "<error : can't generate JSON schema for open typedef>"
generateCode _          _         = "<error : unknown backend>"

-- re-exports
parseType : String -> Maybe (n : Nat ** TNamed n)
parseType = parseTNamed 

deserialize0 : String -> String -> Maybe (td : TDef 0 ** Ty [] td)
deserialize0 tdstr tmstr = 
  do (n**td) <- parseTDef tdstr   
     case n of 
       Z => (\tm => (td ** tm)) <$> deserialize [] [] td tmstr
       _ => Nothing

lib : FFI_Export FFI_JS "" []
lib = Data (n ** TNamed n) "TNamedN" $
      Data (Maybe (n ** TNamed n)) "MaybeTNamedN" $
      Data (Maybe (td : TDef 0 ** Ty [] td)) "MaybeTDefTy" $
      Fun parseType "parseType" $
      Fun deserialize0 "deserialize0" $
      Fun generateCode "generateCode" $
      End
