module Typedefs.Syntax.IndexFree

import Typedefs.Syntax.AST
import TParsec
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

parseNoArg : All (Parser' DefName)
parseNoArg = map (flip MkDefName []) alphas

parseWithArgs : All (Parser' DefName)
parseWithArgs =  map (uncurry MkDefName) $ alphas `and` (map NEList.toList $ nelist alphas)

parseDefName : All (Parser' DefName)
parseDefName = parseNoArg `alt` parseWithArgs

-- parseZero : All (Parser' Expr)
-- parseZero = cmap Zero $ char '0'
--
-- parseOne : All (Parser' Expr)
-- parseOne = cmap One $ char '1'

parseIdent : All (Parser' Expr)
parseIdent = map Ref alphas

parseInfix : Char -> f -> All (Parser' f)
parseInfix c f = cmap f $ char c

parsePower : All (Parser' Power)
parsePower = map PLit decimalNat `alt`
             ?useFix


parseFactor : All (Parser' Factor)
parseFactor = hchainl (map FEmb parsePower) (parseInfix '^' FPow) parsePower

parseTerm : All (Parser' Term)
parseTerm = hchainl (map TEmb parseFactor) (parseInfix '*' TMul) parseFactor

parsePlus : All (Parser' (Expr -> Term -> Expr))
parsePlus = parseInfix '+' ESum

parseExpr : All (Parser' Expr)
parseExpr = hchainl (map EEmb parseTerm) parsePlus parseTerm


parseAnon : All (Parser' Expr)
parseAnon = alts
  [ parseExpr
  , parseIdent
  ]



nameColType : All (Parser' (String, Expr))
nameColType = separator (char ':') alphas parseAnon

parseSimple : All (Parser' Definition)
parseSimple = map Simple parseAnon

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

