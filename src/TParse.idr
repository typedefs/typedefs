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
andbox {s} {t} p q = Induction.map2 {a=Parser' s} {b=Parser' t} (\p, q => Combinators.and p q) p q

tdef : All (Parser' AST.TDef)
tdef = 
  fix (Parser' AST.TDef) $ \ rec => 
    alts [            cmap AST.Void                       $ withSpaces (string "Void")
         ,            cmap AST.Unit                       $ withSpaces (string "Unit")
         , Combinators.map (uncurry AST.Prod)             $ parens (rand (withSpaces (char '*')) (andbox rec rec))
         , Combinators.map (uncurry AST.Sum)              $ parens (rand (withSpaces (char '+')) (andbox rec rec))
         , Combinators.map AST.Var                        $ parens (rand (withSpaces (string "var")) decimalNat)
         , Combinators.map (\(nam,el) => AST.Mu nam [el]) $ parens (rand (withSpaces (string "mu")) (and (withSpaces alphas) rec))
         ]

parseMaybe : (Tokenizer tok, MonadRun mn) =>
        String -> (All (Parser (SizedList tok) tok mn a)) -> Maybe a
parseMaybe str p =
  let tokens = tokenize str in
  let input  = MkSizedList tokens in
  let result = runParser p lteRefl input in
  let valid  = \ s => if Size s == Z then Just (Value s) else Nothing in
  case traverse valid (runMonad result) of
    Just (hd :: _) => Just hd
    _              => Nothing
         