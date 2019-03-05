module ParserUtils

import TParsec
import Data.NEList

%access export

except : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         Tok p -> All (Parser mn p (Tok p))
except t = guard (\t' => (t /= t')) anyTok

notChar : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
          Char -> All (Parser mn p (Tok p))
notChar = except . into



