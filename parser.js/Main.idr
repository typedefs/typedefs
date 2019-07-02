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

generateCode : String -> (n ** TNamed n) -> Either String String
generateCode "haskell"  (n  **tn) = Right $ toString $ generateDefs Haskell tn
generateCode _          _         = Left $ "<error : unsupported backend>"

generateTermSerializers : String -> String -> Either String String
generateTermSerializers backend tdef = parseTNamedEither tdef >>= generateCode backend

generateType : String -> String -> Either String String
generateType backend tdef = parseTNamedEither tdef >>= genType backend
  where
    genType : String -> (n ** TNamed n) -> Either String String
    genType "reasonml" (n   ** tn) = Right $ toString $ generateDefs ReasonML tn
    genType "json"     (Z   ** tn) = Right $ toString $ generate JSONDef tn
    genType "json"     (S _ ** tn) = Left "<error : cannot generate JSON schema for open typedefs>"
    genType _          _           = Left "<error : unsupported backend>"

lib : FFI_Export FFI_JS "" []
lib = Data (Either String String) "EitherStringString" $
      Fun generateTermSerializers "generateTermSerializers" $
      Fun Main.generateType "generateType" $
      End
