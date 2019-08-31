module CLI.CommandLineParser

import Options.Applicative

%default total

public export
data InputFile = StringInput String
               | FileInput String

public export
Show InputFile where
  show  StringInput    = "command line input"
  show (FileInput str) = str

public export
data OutputFile = StdOutput
                | FileOutput String

public export
Show OutputFile where
  show  StdOutput       = "stdout"
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

export
data GenerateTarget = All
                    | TypesOnly
                    | TermsOnly
Show GenerateTarget where
  show All = "--all"
  show TypesOnly = "--types"
  show TermsOnly = "--terms"

parseGenerateTarget : Parser GenerateTarget
parseGenerateTarget = flag' All (long "all")
                  <|> flag' TypesOnly (long "types")
                  <|> flag' TermsOnly (long "terms")
                  <|> pure All -- fallback on `All` if no argument is provided


public export
record TypedefOpts where
  constructor MkTypedefOpts
  input : InputFile
  output : OutputFile
  generate : GenerateTarget

public export
data CommandLineOpts = Help 
                     | GenerateTDefOpt TypedefOpts 
                     | HelpFallback

Show TypedefOpts where
  show (MkTypedefOpts i o t) = "input : " ++ show i ++ "output : " ++ show o ++ " generate: " ++ show t

export
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
      typedefs_parser -s bool.tdef project/typedefs/types.hs

  --stdout : print the output on stdout
    example:
      typedefs_parser -i bool.tdef --stdout | grep "bool"
"""

export
fallbackMessage : String
fallbackMessage = """
No arguments supplied, expected --help or -s SOURCE -d DEST.

Typedefs allows you to define types using very general operations and
generate seralisers and deserialisers for a target language.

If this is your first time head to https://typedefs.com for more information or use --help.
"""

parseTDefOptions : Parser TypedefOpts
parseTDefOptions = [| MkTypedefOpts parseInput parseOutput parseGenerateTarget|]

export
parseProgramOptions : Parser CommandLineOpts
parseProgramOptions = (GenerateTDefOpt <$> parseTDefOptions)
                        <|> flag' Help (long "help" . short 'h')
                        <|> pure HelpFallback


