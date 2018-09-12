module Provider

import TParsec
import TParsec.Running

import Types
import TParseTDef

%language TypeProviders
%default total

provideTP : String -> IO (Provider TDef)
provideTP s = case parseMaybe s tdef of
  Just r => pure $ Provide r
  Nothing => pure $ Error "parse error"

-- FIXME: parse error
-- %provide (typedef : AST.TDef) with provideTP "(mu list (* Unit Unit))"
