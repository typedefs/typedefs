import Typedefs
import Parse
import Backend
import Backend.Utils
import Backend.Haskell

import Options.Applicative

%default total

flag' : a -> (Option FlagParams a -> Option FlagParams a) -> Parser a
flag' d f = OptP (f $ Opt defProps (FlagReader [] d))


data InputFile = StringInput String
               | FileInput String

Show InputFile where
  show StringInput = "command line input"
  show (FileInput str) = str

data OutputFile = StdOutput
                | FileOutput String

Show OutputFile where
  show StdOutput = "stdout"
  show (FileOutput str) = str

stringInput : Parser InputFile
stringInput = StringInput <$> strOption (long "inline" . short 'i')

fileInput : Parser InputFile
fileInput = FileInput <$> strOption (long "source" . short 's')

parseInput : Parser InputFile
parseInput = stringInput <|> fileInput

stdOutput : Parser OutputFile
stdOutput = flag' StdOutput (long "stdout")

fileOutput : Parser OutputFile
fileOutput = FileOutput <$> strOption (long "dest" . short 'd')

parseOutput : Parser OutputFile
parseOutput = fileOutput <|> stdOutput <|> pure StdOutput


record TypedefOpts where
  constructor MkTypedefOpts
  input : InputFile
  output : OutputFile

data CommandLineOpts = Help | GenerateTDefOpt TypedefOpts | HelpFallback

Show TypedefOpts where
  show (MkTypedefOpts i o) = "input : " ++ show i ++ "output : " ++ show o

helpMessage : String
helpMessage = """
Welcome to Typedefs, programming language for types.

Usage:
  typedefs_parser (-i INLINE_TDEF | -s SOURCE) [-d DEST | --stdout]

  --source, -s : path to the input file
    example:
      typedefs_parser -s bool.tdef

  --inline, -i : input as a string inline
    example:
      typedefs_parser -i "(name bool (+ 1 1))" --stdout

  --dest, -d : path to the destination file
    example:
      typedefs_parser -i bool.tdef project/typedefs/types.hs

  --stdout : print the output on stdout
    example:
      typedefs_parser -i bool.tdef --stdout | grep "bool"
"""

fallbackMessage : String
fallbackMessage = """
No arguments supplied, expected --help or -s SOURCE -d DEST.

Typedefs allows you to define types using very general operations and
generate seralizers and deserializers for a target language.

If this is your first time head to https://typedefs.com for more information or use --help.
"""

parseTDefOptions : Parser TypedefOpts
parseTDefOptions = MkTypedefOpts <$> parseInput <*> parseOutput

parseProgramOptions : Parser CommandLineOpts
parseProgramOptions = (GenerateTDefOpt <$> parseTDefOptions) 
                        <|> flag' Help (long "help" . short 'h') 
                        <|> pure HelpFallback


processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseProgramOptions opts
processArgs _ = Left (ErrorMsg "Not enough arguments")

generateTDef : String -> Maybe String
generateTDef tdef = map (\(_ ** tp) => print . generateDefs Haskell $ tp) (parseTNamed tdef)

getInput : InputFile -> IO (Either FileError String)
getInput (StringInput x) = pure (Right x)
getInput (FileInput x) = readFile x

writeOutput : OutputFile -> String -> IO ()
writeOutput StdOutput tdef = putStrLn tdef
writeOutput (FileOutput path) tdef = do Right () <- writeFile path tdef
                                          | Left error => putStrLn ("File write error: " ++ show path)
                                        putStrLn ("Generated typedef at " ++ path)
runWithOptions : TypedefOpts -> IO ()
runWithOptions (MkTypedefOpts input output) = do
  Right typedef <- getInput input
    | Left err => putStrLn ("Filesystem error: " ++ show err)
  case generateTDef typedef of
       Nothing => putStrLn ("Typedef error: " ++ "could not generate typedef")
       Just tdef => writeOutput output tdef

partial
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               GenerateTDefOpt o => runWithOptions o
