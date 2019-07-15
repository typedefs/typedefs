module Main

import Text.PrettyPrint.WL
import TParsec
import public Typedefs
import Parse
import Data.NEList
import public TermParse
import public TermWrite
import Backend
import Backend.Utils
import Backend.Haskell
import Backend.JSON
import Backend.ReasonML

generateTermSerializers : String -> String -> Either String String
generateTermSerializers backend tdef = (resultToEither $ parseTNameds tdef) >>= (genCode backend) 
  where
  genCode : String -> NEList (n ** TNamed n) -> Either String String
  genCode "haskell"  nel = maybeToEither "<error : cannot generate Haskell for open typedefs (shouldn't happen)" $ 
                           print <$> generateDefs Haskell nel
  genCode _          _   = Left "<error : unsupported backend>"

generateType : String -> String -> Either String String
generateType backend tdef = (resultToEither $ parseTNameds tdef) >>= (genType backend) 
  where
  genType : String -> NEList (n ** TNamed n) -> Either String String
  genType "reasonml" nel = maybeToEither "<error : cannot generate ReasonML for open typedefs (shouldn't happen)" $ 
                           print <$> generateDefs ReasonML nel
  genType "json"     nel = maybeToEither "<error : cannot generate JSON schema for open typedefs>" $ 
                           print <$> generate JSONDef nel
  genType _          _   = Left "<error : unsupported backend>"

lib : FFI_Export FFI_JS "" []
lib = Data (Either String String) "EitherStringString" $
      Fun generateTermSerializers "generateTermSerializers" $
      Fun Main.generateType "generateType" $
      End
