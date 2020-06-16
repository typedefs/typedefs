module CLI.CommandLineParser

import Options.Applicative

%default total

public export
data InputFormat =

  ||| Lisp syntax is the traditional lisp-like syntax for Typedefs
  Lispy |

  ||| IndexFree syntax is the new Typedefs syntax
  ||| That looks more like ml-style data declaration
  ||| It has some limitations compared to lispy, but is much more
  ||| familiar to use.
  IndexFree

export
Show InputFormat where
  show Lispy = "Lisp-like syntax"
  show IndexFree = "Typedefs syntax"

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

parseFormat : Parser InputFormat
parseFormat = indexFreeSyntax <|> lispySyntax <|> pure IndexFree
  where
    indexFreeSyntax : Parser InputFormat
    indexFreeSyntax = flag' IndexFree (long "tdef-syntax")
    lispySyntax : Parser InputFormat
    lispySyntax = flag' Lispy (long "s-exp-syntax")

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

public export
record TypedefOpts where
  constructor MkTypedefOpts
  format : InputFormat
  input : InputFile
  output : OutputFile

public export
data CommandLineOpts = Help | GenerateTDefOpt TypedefOpts | HelpFallback

Show TypedefOpts where
  show (MkTypedefOpts s i o) =
    "syntax : " ++ show s ++
    " input : " ++ show i ++
    " output : " ++ show o

export
helpMessage : String
helpMessage = """
Welcome to Typedefs, programming language for types.

Usage:
  typedefs_parser [--tdef-syntax TDEF_SYN | --s-exp-syntax S_EXP_SYN]
                  (--inline -i INLINE_TDEF | -s SOURCE)
                  [--dest -d DEST | --stdout]
  --tdef-syntax | --s-exp-syntax : Select which Typedefs format the
    file is written in.

  --source, -s : path to the input file
    example:
      typedefs_parser -s bool.tdef

  --inline, -i : input as a string inline
    example:
      typedefs_parser -i "Bool := 1 + 1;" --stdout

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
parseTDefOptions = [| MkTypedefOpts parseFormat parseInput parseOutput |]

export
parseProgramOptions : Parser CommandLineOpts
parseProgramOptions = (GenerateTDefOpt <$> parseTDefOptions)
                        <|> flag' Help (long "help" . short 'h')
                        <|> pure HelpFallback


