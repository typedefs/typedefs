module JS.Main

import Text.PrettyPrint.WL
import TParsec
import Data.NEList

import public Typedefs.Typedefs
import public Typedefs.TermParse
import public Typedefs.TermWrite
import        Typedefs.Parse
import        Typedefs.Either
import        Typedefs.Text
import        Typedefs.Backend
import        Typedefs.Backend.Data
import        Typedefs.Backend.Utils
import        Typedefs.Backend.Haskell
import        Typedefs.Backend.JSON
import        Typedefs.Backend.ReasonML

generateTermSerialisers : String -> String -> Either String String
generateTermSerialisers backend tdef = (resultToEither $ parseTopLevel tdef) >>= (genCode backend)
  where
  genCode : String -> TopLevelDef -> Either String String
  genCode "haskell"  nel = printOrShowError $ generateDefs Haskell nel
  genCode _          _   = Left "<error : unsupported backend>"

generateType : String -> String -> Either String String
generateType backend tdef = (resultToEither $ parseTopLevel tdef) >>= (genType backend)
  where
  genType : String -> TopLevelDef -> Either String String
  genType "reasonml" nel = printOrShowError $ generateDefs ReasonML nel
  genType "json"     nel = maybeToEither "<error : cannot generate JSON schema for open typedefs>" $
                           Text.print <$> generate JSONDef (typedefs nel)
  genType _          _   = Left "<error : unsupported backend>"

lib : FFI_Export FFI_JS "" []
lib = Data (Either String String) "EitherStringString" $
      Fun generateTermSerialisers "generateTermSerialisers" $
      Fun Main.generateType "generateType" $
      End
