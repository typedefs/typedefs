module Typedefs.Syntax

import Typedefs.Typedefs

import Typedefs.Syntax.Compiler
import Typedefs.Syntax.IndexFree
import Typedefs.Syntax.AST
import Data.NEList

export
parseSyntaxFile : String -> Either String (NEList (n ** TNamed n))
parseSyntaxFile input = do list <- maybeToEither "Could not parse" (parseDefList input)
                           traverse compileEither list

