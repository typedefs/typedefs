module TermCodec

import Data.Vect

import TParsec
import TParsec.Running

import Typedefs
import Types

%default total
%access public export

-- deserialization

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok Char)

data HasParsers : Vect n Type -> Nat -> Type where
  Nil : HasParsers Nil m
  (::) : {xs : Vect n Type} -> Parser' x m -> HasParsers xs m -> HasParsers (x :: xs) m

mutual
  muParser : (ts : Vect n Type) -> All (HasParsers ts :-> Parser' (Mu ts td))
  muParser {td} ts ps = assert_total $ map (\ty => Inn {tvars = ts} {m = td} ty) $ 
                        parens (rand (string "inn") 
                                     (withSpaces $ chooseParser td ((Mu ts td)::ts) ((muParser ts ps)::ps)))
  
  chooseParser : (t : TDef n) -> (ts : Vect n Type) -> All (HasParsers ts :-> Parser' (Ty ts t))
  chooseParser T0                    _         _         = fail
  chooseParser T1                    _         _         = cmap () $ string "()"
  chooseParser (TSum [x,y])          ts        ps        = 
    parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts ps)) 
                 (rand (string "right") (withSpaces $ chooseParser y ts ps))
  chooseParser (TSum (x::y::z::zs))  ts        ps        = 
    parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts ps)) 
                 (rand (string "right") (withSpaces $ assert_total $ chooseParser (TSum (y::z::zs)) ts ps))
  chooseParser (TProd [x,y])         ts        ps        = 
    parens $ rand (string "both") (and (withSpaces $ chooseParser x ts ps) 
                                       (withSpaces $ chooseParser y ts ps))
  chooseParser (TProd (x::y::z::zs)) ts        ps        = 
    parens $ rand (string "both") (and (withSpaces $ chooseParser x ts ps) 
                                       (withSpaces $ assert_total $ chooseParser (TProd (y::z::zs)) ts ps))
  chooseParser (TVar FZ)             (_::_)    (p::_)    = p
  chooseParser (TVar (FS FZ))        (_::_::_) (_::p::_) = p
  chooseParser (TVar (FS (FS i)))    (_::ts)   (_::ps)   = chooseParser (TVar (FS i)) ts ps
  chooseParser (TMu _ td)            ts        ps        = 
    map (\ty => Inn {tvars = ts} {m = args td} ty) $ 
    parens (rand (string "inn") 
                 (withSpaces $ assert_total $ chooseParser (args td) ((Mu ts (args td))::ts) ((muParser ts ps)::ps)))
  chooseParser (TName _ td)          ts        ps        = chooseParser td ts ps

deserialize : (ts : Vect n Type) -> All (HasParsers ts) -> (td : TDef n) -> String -> Maybe (Ty ts td)
deserialize ts ps td s  = 
  parseMaybe s (chooseParser td ts ps)
