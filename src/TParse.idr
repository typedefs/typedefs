module TParse

import TParsec
import TParsec.Running
import TParsec.NEList

import AST as AST
import Types

%default total

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