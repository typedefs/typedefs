module Typedefs.Syntax.IndexFree

import Typedefs.Syntax.AST
import TParsec
import TParsec.Running
import Data.NEList

separator : (Alternative mn, Monad mn) =>
            All (Parser mn p s :-> Parser mn p a :-> Parser mn p b :-> Parser mn p (a, b))
separator sep a b = a `and` (sep `rand` b)

-- this should be in tparsec
sepBy : (Alternative mn, Monad mn) =>
        All (Parser mn p a :-> Parser mn p s :-> Parser mn p (NEList a))
sepBy parser sep = map (flip MkNEList []) parser
             `alt` map (uncurry MkNEList) (parser `and` (map NEList.toList $ nelist (sep `rand` parser)))

Parser' : Type -> Nat -> Type
Parser' = Parser (TParsecT () Void Maybe) chars

record Language (n : Nat) where
  constructor MkLanguage
  _expr   : Parser' Expr n
  _term   : Parser' Term n
  _factor : Parser' Factor n
  _power  : Parser' Power n

parseNoArg : All (Parser' DefName)
parseNoArg = map (flip MkDefName []) alphas

parseWithArgs : All (Parser' DefName)
parseWithArgs =  map (uncurry MkDefName) $ alphas `and` (map NEList.toList $ nelist alphas)

parseDefName : All (Parser' DefName)
parseDefName = parseNoArg `alt` parseWithArgs

parseIdent : All (Parser' Expr)
parseIdent = map Ref alphas

parseInfix : Char -> f -> All (Parser' f)
parseInfix c f = cmap f $ char c

parsePlus : All (Parser' (Expr -> Term -> Expr))
parsePlus = parseInfix '+' ESum

language : All (Language)
language = fix (Language) $ \rec => let 
  parsePower = map PLit decimalNat `alt` map PEmb (parens (Nat.map {a=Language} _expr rec))

  parseFactor = hchainl (map FEmb (parsePower)) (parseInfix '^' FPow) parsePower

  parseTerm = hchainl (map TEmb (parseFactor)) (parseInfix '*' TMul) parseFactor

  parseExpr = hchainl (map EEmb (parseTerm)) parsePlus parseTerm

  in MkLanguage (parseExpr) (parseTerm) (parseFactor) (parsePower)


nameColType : All (Parser' (String, Expr))
nameColType = separator (char ':') alphas (_expr language)

parseSimple : All (Parser' Definition)
parseSimple = map Simple (_expr language)

parseEnum : All (Parser' Definition)
parseEnum = map (Enum . NEList.toList) $ nameColType `sepBy` char '|'

parseRecord : All (Parser' Definition)
parseRecord = between (char '{') (char '}') $
              map (Record . NEList.toList) $ nameColType `sepBy` char ','


parseDef : All (Parser' Definition)
parseDef = alts
  [ parseSimple
  , parseEnum
  , parseRecord
  ]

parseTopDef : All (Parser' TopLevelDef)
parseTopDef = map (uncurry MkTopLevelDef) $ separator (string ":=") parseDefName parseDef

parseDefinitions : All (Parser' (NEList TopLevelDef))
parseDefinitions = nelist parseTopDef

