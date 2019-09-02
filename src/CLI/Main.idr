module CLI.Main

import Typedefs.Typedefs
import Typedefs.Parse
import Typedefs.Either
import Typedefs.Backend
import Typedefs.Backend.Utils
import Typedefs.Backend.Haskell
import CLI.CommandLineParser

import Options.Applicative
import Control.Lens.Setter
import Data.NEList
import TParsec.Result

%default total

processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseProgramOptions opts
processArgs  _          = Left (ErrorMsg "Not enough arguments")

writeOutput : OutputFile -> String -> IO ()
writeOutput  StdOutput        out = putStrLn out
writeOutput (FileOutput path) out = do Right () <- writeFile path out
                                         | Left error => putStrLn ("File write error: " ++ show path)
                                       putStrLn ("Generated typedef at " ++ path)

getInput : InputFile -> IO (Either FileError String)
getInput (StringInput x) = pure (Right x)
getInput (FileInput x)   = readFile x

parseAndGenerateTDef : String -> Either String String
parseAndGenerateTDef tdef = (resultToEither $ parseTNameds tdef)
                        >>= Either.bimap show Utils.print . generateDefs Haskell

runWithOptions : TypedefOpts -> IO ()
runWithOptions (MkTypedefOpts input output) = do
  Right typedef <- getInput input
    | Left err => putStrLn ("Filesystem error: " ++ show err)
  case parseAndGenerateTDef typedef of
    Left err => putStrLn ("Typedef error: " ++ err)
    Right defs => writeOutput output defs

partial
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               GenerateTDefOpt o => runWithOptions o
