module JS.Main

import Text.PrettyPrint.WL
import TParsec
import Data.NEList

import public Typedefs.Typedefs
import public Typedefs.TermParse
import public Typedefs.TermWrite
import        Typedefs.Parse
import        Typedefs.Either
import        Typedefs.Backend
import        Typedefs.Backend.Utils
import        Typedefs.Backend.Haskell
import        Typedefs.Backend.JSON
import        Typedefs.Backend.ReasonML

generateTermSerialisers : String -> String -> Either String String
generateTermSerialisers backend tdef = (resultToEither $ parseTNameds tdef) >>= (genCode backend)
  where
  genCode : String -> NEList (n ** TNamed n) -> Either String String
  genCode "haskell"  nel = bimap show print $ generateDefs Haskell nel
  genCode _          _   = Left "<error : unsupported backend>"

generateType : String -> String -> Either String String
generateType backend tdef = (resultToEither $ parseTNameds tdef) >>= (genType backend)
  where
  genType : String -> NEList (n ** TNamed n) -> Either String String
  genType "reasonml" nel = bimap show print $ generateDefs ReasonML nel
  genType "json"     nel = maybeToEither "<error : cannot generate JSON schema for open typedefs>" $
                           Backend.Utils.print <$> generate JSONDef nel
  genType _          _   = Left "<error : unsupported backend>"

lib : FFI_Export FFI_JS "" []
lib = Data (Either String String) "EitherStringString" $
      Fun generateTermSerialisers "generateTermSerialisers" $
      Fun Main.generateType "generateType" $
      End
