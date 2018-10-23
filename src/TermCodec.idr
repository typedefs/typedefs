module TermCodec

import Data.Vect

import TParsec
import TParsec.Running

import Typedefs
import Types

%default total
%access public export

mutual 

  serializeMu : {ts : Vect n (t: Type ** t -> String)} -> Mu (map DPair.fst ts) td -> String
  serializeMu {ts} {td} (Inn x) = "(inn " ++ (assert_total $ serialize {ts=(Mu (map DPair.fst ts) td ** serializeMu)::ts} td x) ++ ")"

  serialize : {ts : Vect n (t: Type ** t -> String)} -> (t : TDef n) -> (tm : Ty (map DPair.fst ts) t) -> String
  serialize                    T1                    ()        = "()"
  serialize                    (TSum [x,_])          (Left l)  = "(left "  ++ serialize x l ++ ")"
  serialize                    (TSum [_,y])          (Right r) = "(right " ++ serialize y r ++ ")"
  serialize                    (TSum (x::_::_::_))   (Left l)  = "(left "  ++ serialize x l ++ ")"
  serialize                    (TSum (_::y::z::zs))  (Right r) = "(right " ++ serialize (TSum (y::z::zs)) r ++ ")"
  serialize                    (TProd [x,y])         (a, b)    = "(both "  ++ serialize x a ++ " " ++ serialize y b ++ ")"
  serialize                    (TProd (x::y::z::zs)) (a, b)    = "(both "  ++ serialize x a ++ " " ++ serialize (TProd (y::z::zs)) b ++ ")"
  serialize {ts=   (_**f)::_ } (TVar FZ)             x         = f x
  serialize {ts=_::(_**f)::_ } (TVar (FS FZ))        x         = f x 
  serialize {ts=        _::ts} (TVar (FS (FS i)))    x         = serialize {ts} (TVar (FS i)) x
  serialize {ts}               (TMu _ td)            (Inn x)   = 
    "(inn " ++ serialize {ts=((Mu (map DPair.fst ts) (args td)) ** serializeMu)::ts} (args td) x ++ ")"
  serialize                    (TName _ td)          x         = serialize td x

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok Char)

infixr 1 :~>
(:~>) : {i : Type} -> (a : i -> Type) -> (b : (j : i) -> a j -> Type) -> (i -> Type)
(:~>) a b i = (ai : a i) -> b i ai

mutual
  muParser : All ((\j => Vect n (t : Type ** (Parser' t) j)) :~> (\j, ts => Parser' (Mu (map DPair.fst ts) td) j))
  muParser {td} ts = assert_total $ map (\ty => Inn {tvars = map DPair.fst ts} {m = td} ty) $ 
                     parens (rand (string "inn") (withSpaces $ chooseParser td ((Mu (map DPair.fst ts) td ** muParser ts)::ts)))
  
  chooseParser : (t : TDef n) -> All ((\j => Vect n (t : Type ** (Parser' t) j)) :~> (\j, ts => Parser' (Ty (map DPair.fst ts) t) j))
  chooseParser T0                    _              = fail
  chooseParser T1                    _              = cmap () $ string "()"
  chooseParser (TSum [x,y])          ts             = parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts)) 
                                                                   (rand (string "right") (withSpaces $ chooseParser y ts))
  chooseParser (TSum (x::y::z::zs))  ts             = parens $ sum (rand (string "left")  (withSpaces $ chooseParser x ts)) 
                                                                   (rand (string "right") (withSpaces $ assert_total $ chooseParser (TSum (y::z::zs)) ts))
  chooseParser (TProd [x,y])         ts             = parens $ rand (string "both") (and (withSpaces $ chooseParser x ts) 
                                                                                         (withSpaces $ chooseParser y ts))
  chooseParser (TProd (x::y::z::zs)) ts             = parens $ rand (string "both") (and (withSpaces $ chooseParser x ts) 
                                                                                         (withSpaces $ assert_total $ chooseParser (TProd (y::z::zs)) ts))
  chooseParser (TVar FZ)             (   (_**p)::_) = p
  chooseParser (TVar (FS FZ))        (_::(_**p)::_) = p
  chooseParser (TVar (FS (FS i)))    (_::ts)        = chooseParser (TVar (FS i)) ts
  chooseParser (TMu _ td)            ts             = map (\ty => Inn {tvars = map DPair.fst ts} {m = args td} ty) $ 
                                                      parens (rand (string "inn") 
                                                                   (withSpaces $ assert_total $ chooseParser (args td) ((Mu (map DPair.fst ts) (args td) ** muParser ts)::ts)))
  chooseParser (TName _ td)          ts             = chooseParser td ts