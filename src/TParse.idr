module TParse

import TParsec
import TParsec.Running
import TParsec.NEList

import AST as AST
import Types

%default total
%access public export

Parser' : Type -> Nat -> Type
Parser' = Parser (SizedList Char) Char Maybe

tdefAst : All (Parser' AST.TDef)
tdefAst = 
  fix (Parser' AST.TDef) $ \rec => 
    alts [ cmap AST.Void                                      $ withSpaces (string "Void")
         , cmap AST.Unit                                      $ withSpaces (string "Unit")
         , map (\(x,nel) => AST.Prod x (head nel) (tail nel)) $ parens (rand (withSpaces (char '*')) 
                                                                             (map2 {a=Parser' _} {b=Parser' _} 
                                                                                   (\p, q => and p q) 
                                                                                   (map {a=Parser' _} withSpaces rec)
                                                                                   (map {a=Parser' _} (nelist . withSpaces) rec)))
         , map (\(x,nel) => AST.Sum x (head nel) (tail nel))  $ parens (rand (withSpaces (char '+')) 
                                                                             (map2 {a=Parser' _} {b=Parser' _} 
                                                                                   (\p, q => and p q) 
                                                                                   (map {a=Parser' _} withSpaces rec)
                                                                                   (map {a=Parser' _} (nelist . withSpaces) rec)))
         , map AST.Var                                        $ parens (rand (withSpaces (string "var")) (withSpaces decimalNat))
         , map (\(nam,nel) => AST.Mu nam (map snd $ NEList.toList nel)) $ 
           parens (rand (withSpaces (string "mu")) 
                  (and (withSpaces alphas) 
                       (map {a=Parser' _} (\t => nelist $ withSpaces $ parens $ and (withSpaces alphas) t) rec)))
         ]

-- TODO included in latest TParsec         
parseMaybe : (Tokenizer tok, MonadRun mn) =>
        String -> (All (Parser (SizedList tok) tok mn a)) -> Maybe a
parseMaybe str p =
  let tokens = tokenize str
      input  = MkSizedList tokens
      result = runParser p lteRefl input
      valid  = \s => if Size s == Z then Just (Value s) else Nothing
     in
  traverse valid (runMonad result) >>= head'
