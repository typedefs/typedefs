module Typedefs.Text

import Typedefs.Either
import Text.PrettyPrint.WL

-- Doc helpers
||| Print a document with a width of 80 symbols.
export
print : Doc -> String
print = toString 1 80

||| Map both sides of an either to a string, the left side traditionally represents an error
export
printOrShowError : (Show err) => Either err Doc -> Either String String
printOrShowError = bimap show print

||| Vertically concatenate a list of documents with two newlines (i.e. one empty line) as separator.
export
vsep2 : List Doc -> Doc
vsep2 = vsep . punctuate line
