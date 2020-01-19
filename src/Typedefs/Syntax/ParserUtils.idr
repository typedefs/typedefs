module Typedefs.Syntax.ParserUtils

import Typedefs.Syntax.AST
import TParsec
import TParsec.Running
import Data.NEList

-- All this should probably be in tparsec

export
sepBy : (Alternative mn, Monad mn) =>
        All (Parser mn p a :-> Parser mn p s :-> Parser mn p (NEList a))
sepBy parser sep = map (uncurry MkNEList) (parser `and` (map NEList.toList $ nelist (sep `rand` parser)))
             `alt` map (flip MkNEList []) parser

export
linebreak : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
            All (Parser mn p (Tok p))
linebreak = anyOf (map into $ unpack "\r\n")

export
parseLines : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p a :-> Parser mn p (NEList a))
parseLines p = p `sepBy` (string ";\n")
