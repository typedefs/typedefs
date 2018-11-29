module Provider

import Data.SortedMap 

import TParsec
import TParsec.Running

import Typedefs
import Parse

%language TypeProviders
%default total

provideTP : String -> IO (Provider (n ** TDef n))
provideTP s = case parseMaybe s tdef of
  Just r => pure $ Provide r
  Nothing => pure $ Error "parse error"

-- FIXME: parse error
-- %provide (typedef : AST.TDef) with provideTP "(mu list (* Unit Unit))"
