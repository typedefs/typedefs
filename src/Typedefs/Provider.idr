module Typedefs.Provider

import Data.SortedMap

import TParsec
import TParsec.Running

import Typedefs.Typedefs
import Typedefs.Parse

%language TypeProviders
%default total

provideTP : String -> IO (Provider (n ** TDefR n))
provideTP s = case parseMaybe s tdefRec of
  Just r => pure $ Provide r
  Nothing => pure $ Error "parse error"

-- FIXME: parse error
-- %provide (typedef : AST.TDef) with provideTP "(mu list (* Unit Unit))"
