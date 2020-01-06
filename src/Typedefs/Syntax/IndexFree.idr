module Typedefs.Syntax.IndexFree

import Typedefs.Syntax.AST
import TParsec
import TParsec.Running
import Data.NEList

||| This consumes at least one space
whitespaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
              All (Parser mn p ())
whitespaces {p} = cmap () $ spaces {p}

ignoreSpaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
               All (Parser mn p a :-> Parser mn p a)
ignoreSpaces parser = whitespaces `roptand` (parser `landopt` whitespaces)

separator : (Alternative mn, Monad mn) =>
            All (Parser mn p s :-> Parser mn p a :-> Parser mn p b :-> Parser mn p (a, b))
separator sep a b = a `and` (sep `rand` b)

-- this should be in tparsec
sepBy : (Alternative mn, Monad mn) =>
        All (Parser mn p a :-> Parser mn p s :-> Parser mn p (NEList a))
sepBy parser sep = map (uncurry MkNEList) (parser `and` (map NEList.toList $ nelist (sep `rand` parser)))
             `alt` map (flip MkNEList []) parser

export
Parser' : Type -> Nat -> Type
Parser' = Parser (TParsecT () Void Maybe) chars

record Language (n : Nat) where
  constructor MkLanguage
  _expr   : Parser' Expr n
  _term   : Parser' Term n
  _factor : Parser' Factor n
  _power  : Parser' Power n
  _appli  : Parser' Appli n

parseNoArg : All (Parser' DefName)
parseNoArg = map (flip MkDefName []) alphas

parseWithArgs : All (Parser' DefName)
parseWithArgs =  map (uncurry MkDefName) $ ignoreSpaces alphas `and` (map NEList.toList $ alphas `sepBy` whitespaces)

parseDefName : All (Parser' DefName)
parseDefName = parseWithArgs `alt` parseNoArg

parseIdent : All (Parser' Power)
parseIdent = map PRef (ignoreSpaces alphas)

parseInfix : Char -> f -> All (Parser' f)
parseInfix c f = cmap f $ ignoreSpaces (char c)

parsePlus : All (Parser' (Expr -> Term -> Expr))
parsePlus = parseInfix '+' ESum

parseIdApp : All (Parser' (NEList String))
parseIdApp = (alphas `sepBy` whitespaces)

language : All (Language)
language = fix Language $ \rec => let

  parsePower = alts [
      map PLit decimalNat
    , map PRef alphas
    -- parse type application using the `expr` parser recursively
    , map PEmb (parens (Nat.map {a=Language} _appli rec))
    ]

  parseFactor = hchainl (map FEmb parsePower) (parseInfix '^' FPow) parsePower

  parseTerm = hchainl (map TEmb parseFactor) (parseInfix '*' TMul) parseFactor

  parseExpr = hchainl (map EEmb parseTerm) parsePlus parseTerm

  parseApplication = hchainr (alphas) (cmap (\a, b => AST.App a (AEmb b)) spaces) parseExpr

  in MkLanguage parseExpr parseTerm parseFactor parsePower parseApplication


nameColType : All (Parser' (String, Appli))
nameColType = separator (ignoreSpaces $ char ':') alphas (_appli language)

parseSimple : All (Parser' Definition)
parseSimple = map Simple (_appli language)

parseEnum : All (Parser' Definition)
parseEnum = Combinators.map (Enum . NEList.toList) $ nameColType `sepBy` (ignoreSpaces $ char '|')

parseRecord : All (Parser' Definition)
parseRecord = between (char '{') (char '}') $
              Combinators.map (Record . NEList.toList) $ nameColType `sepBy` (ignoreSpaces $ char ',')

parseDef : All (Parser' Definition)
parseDef = alts
  [ parseEnum
  , parseRecord
  , parseSimple
  ]

topDefParser : All (Parser' TopLevelDef)
topDefParser = map (uncurry MkTopLevelDef) $ separator (ignoreSpaces $ string ":=") parseDefName parseDef

definitionParser : All (Parser' (NEList TopLevelDef))
definitionParser = nelist topDefParser

export
parseMaybeExpr : String -> Maybe Expr
parseMaybeExpr input = parseMaybe input (_expr language)


export
parseMaybeTopDef : String -> Maybe TopLevelDef
parseMaybeTopDef input = parseMaybe input topDefParser

export
parseDefList : String -> Maybe (NEList TopLevelDef)
parseDefList input = parseMaybe input definitionParser

