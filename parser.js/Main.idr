module Main

import Text.PrettyPrint.WL
import TParsec
import public Typedefs
import Parse
import public TermParse
import public TermWrite
import Backend
import Backend.Utils
import Backend.Haskell
import Backend.JSON
import Backend.ReasonML

generateTermSerializers : String -> String -> Either String String
generateTermSerializers backend tdef = map (genCode backend) (convertToEither $ parseTNamed tdef)
  where
  genCode : String -> (n ** TNamed n) -> String
  genCode "haskell"  (n  **tn) = toString $ generateDefs Haskell tn
  genCode _          _         = "<error : unsupported backend>"

generateType : String -> String -> Either String String
generateType backend tdef = map (genType backend) (convertToEither $ parseTNamed tdef)
  where
  genType : String -> (n ** TNamed n) -> String
  genType "reasonml" (n   ** tn) = toString $ generateDefs ReasonML tn
  genType "json"     (Z   ** tn) = toString $ generate JSONDef tn
  genType "json"     (S _ ** tn) = "<error : cannot generate JSON schema for open typedefs>"
  genType _          _           = "<error : unsupported backend>"

lib : FFI_Export FFI_JS "" []
lib = Data (Either String String) "EitherStringString" $
      Fun generateTermSerializers "generateTermSerializers" $
      Fun Main.generateType "generateType" $
      End
