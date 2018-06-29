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

andbox : All (Box (Parser' s) :-> Box (Parser' t) :-> Box (Parser' (s, t)))
andbox {s} {t} p q = map2 {a=Parser' s} {b=Parser' t} (\p, q => and p q) p q

tdefAst : All (Parser' AST.TDef)
tdefAst = 
  fix (Parser' AST.TDef) $ \rec => 
    alts [ cmap AST.Void                      $ withSpaces (string "Void")
         , cmap AST.Unit                      $ withSpaces (string "Unit")
         , map (uncurry AST.Prod)             $ parens (rand (withSpaces (char '*')) (andbox rec rec))
         , map (uncurry AST.Sum)              $ parens (rand (withSpaces (char '+')) (andbox rec rec))
         , map AST.Var                        $ parens (rand (withSpaces (string "var")) decimalNat)
         , map (\(nam,el) => AST.Mu nam [el]) $ parens (rand (withSpaces (string "mu")) (and (withSpaces alphas) rec))
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
