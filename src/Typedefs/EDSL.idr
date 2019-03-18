
module Typedefs.EDSL

import Typedefs
import Data.Vect

import Names

Void : TDef n
Void = T0

Unit : TDef n
Unit = T1

private
consMult : TDef n -> Vect (S k) (TDef n) -> TDef n
consMult lhs rhs = TProd (lhs :: rhs)

(*) : TDef n -> Vect (S k) (TDef n) -> TDef n
(*) = consMult

consAdd : TDef n -> Vect (S k) (TDef n) -> TDef n
consAdd lhs rhs = TSum (lhs :: rhs)

infixr 6 +:

(+:) : TDef n -> Vect (S k) (TDef n) -> TDef n
(+:) = consAdd

-- (+) : TDef n -> TDef n -> TDef n
-- (+) lhs rhs = TSum [lhs, rhs]

(+) : TNamed n -> TNamed n -> TDef n
(+) lhs rhs = TSum [def lhs, def rhs]

syntax [lhs] "x" [rhs] = TProd (lhs ++ rhs)
syntax [name] ":=" [var] = TName name var

private
natToFin : (n : Nat) -> Fin (S n)
natToFin Z = FZ
natToFin (S k) = FS $ natToFin k

var : Name -> TDef (S n)
var str {n} = TVar $ Typedefs.EDSL.natToFin n

mu : TDef (S n) -> TDef n
mu = ?mu_holw


maybe : TNamed 1
maybe = "Maybe" := ("Nothing" := Unit + "Just" := var "a")

lists : TNamed 1
lists = "List" := mu ("Nil" := Unit + "List" := var "a")


