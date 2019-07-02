module Main

import Typedefs
import Parse
import Backend
import Backend.Utils
import Backend.Haskell
import CommandLine

import Text.PrettyPrint.WL
import Options.Applicative
import Control.Lens.Setter
import TParsec.Result

%default total

%default total

processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseProgramOptions opts
processArgs _ = Left (ErrorMsg "Not enough arguments")

writeOutput : OutputFile -> String -> IO ()
writeOutput StdOutput tdef = putStrLn tdef
writeOutput (FileOutput path) tdef = do Right () <- writeFile path tdef
                                          | Left error => putStrLn ("File write error: " ++ show path)
                                        putStrLn ("Generated typedef at " ++ path)
getInput : InputFile -> IO (Either FileError String)
getInput (StringInput x) = pure (Right x)
getInput (FileInput x) = readFile x

parseAndGenerateTDef : String -> Either String String
parseAndGenerateTDef tdef = map (\(_ ** tp) => print . generateDefs Haskell $ tp) (parseTNamedEither tdef)

runWithOptions : TypedefOpts -> IO ()
runWithOptions (MkTypedefOpts input output) = do
  Right typedef <- getInput input
    | Left err => putStrLn ("Filesystem error: " ++ show err)
  case parseAndGenerateTDef typedef of
    Left err => putStrLn ("Typedef error: " ++ err)
    Right tdef => writeOutput output tdef

partial
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               GenerateTDefOpt o => runWithOptions o
