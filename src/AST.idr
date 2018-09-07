module AST

import Types

%default total
%access public

export

-- TODO placeholder to help get the parser working; to be superseded by actual TDef
data TDef
   = Void
   | Unit
   | Prod TDef TDef (List TDef)
   | Sum  TDef TDef (List TDef)
   | Var  Nat
   | Mu   Name (List TDef)

Show TDef where
  show Void             = "Void"
  show Unit             = "Unit"
  show (Prod  s1 s2 ss) = "(Prod "  ++ show s1 ++ " " ++ show s2 
                          ++ (if size ss == 0 then "" 
                                              else " " ++ unwords (assert_total $ map show ss)) 
                          ++ ")"
  show (Sum   s1 s2 ss) = "(Sum "   ++ show s1 ++ " " ++ show s2
                          ++ (if size ss == 0 then "" 
                                              else " " ++ unwords (assert_total $ map show ss))
                          ++ ")"
  show (Mu    s1 ts)    = "(Mu "    ++ show s1 ++ " " ++ assert_total (show ts) ++ ")"
  show (Var   n)        = "(Var "   ++ show n                                   ++ ")"
