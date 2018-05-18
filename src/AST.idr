module AST

import Types

%access public

export

-- TODO placeholder to help get the parser working; to be superseded by actual TDef
data TDef
   = Void
   | Unit
   | Prod TDef TDef
   | Sum  TDef TDef
   | Mu   Name TDef

Show TDef where
  show Void           = "Void"
  show Unit           = "Unit"
  show (Prod  s1 s2)  = "(Prod "  ++ show s1 ++ " " ++ show s2 ++ ")"
  show (Sum   s1 s2)  = "(Sum "   ++ show s1 ++ " " ++ show s2 ++ ")"
  show (Mu    s1 s2)  = "(Mu "    ++ show s1 ++ " " ++ show s2 ++ ")"
