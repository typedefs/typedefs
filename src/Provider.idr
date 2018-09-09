module Provider

import TParsec
import TParsec.Running

import AST
import Types
import TParse

%language TypeProviders
%default total

provideTP : String -> IO (Provider AST.TDef)
provideTP s = case parseMaybe s tdefAst of
  Just r => pure $ Provide r
  Nothing => pure $ Error "parse error"

-- FIXME: parse error
-- %provide (typedef : AST.TDef) with provideTP "(mu list (* Unit Unit))"
