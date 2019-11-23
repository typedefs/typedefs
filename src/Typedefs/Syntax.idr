module Typedefs.Syntax

import Typedefs.Typedefs
import Typedefs.Backend.Specialisation

import Data.NEList


data SyntaxDef = Zero 
               | One
               | Plus (List SyntaxDef)
               | Times (List SyntaxDef)
               | Constructor (List (String, SyntaxDef))
               | App String (List SyntaxDef)
               | Identifier String

record TopLevelDef where
  constructor MkTopLevelDef
  Name : String
  Variables : List String
  Def : SyntaxDef

toTDef : SyntaxDef -> Maybe (n ** TDef n)
toTDef Zero = Just (0 ** T0)
toTDef One = Just (0 ** T1)
toTDef (Plus xs) = let s = traverse toTDef xs in ?whatSUm
toTDef (Times xs) = ?watProd -- TProd <$> map toTDef xs
toTDef (Constructor x) = ?watMu -- TMu <$> map ?thing x
toTDef (App n xs) = let s = traverse toTDef xs in ?whut
toTDef (Identifier x) = ?toTDef_rhs_7
