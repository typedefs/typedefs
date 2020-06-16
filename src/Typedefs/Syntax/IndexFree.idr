module Typedefs.Syntax.IndexFree

-- Syntax
import Typedefs.Syntax.AST
import Typedefs.Syntax.ParserUtils

-- TParsec
import TParsec
import TParsec.Running
import Data.NEList

||| This consumes at least one space
whitespaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
              All (Parser mn p ())
whitespaces {p} = cmap () $ anyOf {p} (map into $ unpack " \t")

ignoreSpaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
               All (Parser mn p a :-> Parser mn p a)
ignoreSpaces = withSpaces

separator : (Alternative mn, Monad mn) =>
            All (Parser mn p s :-> Parser mn p a :-> Parser mn p b :-> Parser mn p (a, b))
separator sep a b = a `and` (sep `rand` b)

export
Parser' : Type -> Nat -> Type
Parser' = Parser (TParsecT () Void Maybe) chars

record Language (n : Nat) where
  constructor MkLanguage
  _expr   : Parser' Expr n
  _term   : Parser' Term n
  _factor : Parser' Factor n
  _appli  : Parser' Appli n
  _power  : Parser' Val n

parseNoArg : All (Parser' DefName)
parseNoArg = map (flip MkDefName []) alphas

parseWithArgs : All (Parser' DefName)
parseWithArgs =  Combinators.map (uncurry MkDefName) $ ignoreSpaces alphas `and` (Combinators.map NEList.toList $ alphas `sepBy` whitespaces)

parseDefName : All (Parser' DefName)
parseDefName = parseWithArgs `alt` parseNoArg

parseIdent : All (Parser' Val)
parseIdent = map PRef (ignoreSpaces alphas)

parseInfix : Char -> f -> All (Parser' f)
parseInfix c f = cmap f $ ignoreSpaces (char c)

-- Definition := name ':=' expr | enum
-- Enum       := name : expr (| name : expr)*
-- expr       := expr + term
-- term       := term * prod
-- prod       := prod ^ app
-- app        := app pow
-- pow        := [0-9]+ | name | (expr)

language : All (Language)
language = fix Language $ \rec => let

  parseVal = alts [
      map PLit decimalNat
    , map PRef alphas
    -- parse type application using the `expr` parser recursively
    , map PEmb (parens (Nat.map {a=Language} _expr rec))
    ]

  parseApplication = hchainl (map AEmb parseVal) (cmap AST.App spaces) parseVal

  parseFactor = hchainl (map FEmb parseApplication) (parseInfix '^' FPow) parseApplication

  parseTerm = hchainl (map TEmb parseFactor) (parseInfix '*' TMul) parseFactor

  parseExpr = hchainl (map EEmb parseTerm) (parseInfix '+' ESum) parseTerm

  in MkLanguage parseExpr parseTerm parseFactor parseApplication parseVal


nameColType : All (Parser' (String, Expr))
nameColType = separator (ignoreSpaces $ char ':') alphas (_expr language)

parseSimple : All (Parser' Definition)
parseSimple = map Simple (_expr language)

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
definitionParser = nelist $ topDefParser `land` (withSpaces (char ';'))

export
parseMaybeExpr : String -> Maybe Expr
parseMaybeExpr input = parseMaybe input (_expr language)

export
parseMaybeTopDef : String -> Maybe TopLevelDef
parseMaybeTopDef input = parseMaybe input topDefParser

export
parseDefList : String -> Maybe (NEList TopLevelDef)
parseDefList input = parseMaybe input definitionParser
