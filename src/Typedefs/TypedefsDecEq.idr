module Typedefs.TypedefsDecEq

import Data.Vect
import Typedefs.Names
import Typedefs.Typedefs

%default total
%access public export

-- injectivity proofs

tsumInj : {a : Vect (2+n) (TDef k)} -> {b : Vect (2+m) (TDef k)} -> TSum a = TSum b -> a = b
tsumInj Refl = Refl

tprodInj : {a : Vect (2+n) (TDef k)} -> {b : Vect (2+m) (TDef k)} -> TProd a = TProd b -> a = b
tprodInj Refl = Refl

tvarInj : {i, j : Fin (S n)} -> TVar i = TVar j -> i = j
tvarInj Refl = Refl

tmuInj : {a : Vect k1 (Name, TDef (S n))} -> {b : Vect k2 (Name, TDef (S m))} -> TMu a = TMu b -> a = b
tmuInj Refl = Refl

tappInjNamed : {t : TNamed k} -> {u : TNamed k1} -> {a : Vect k (TDef n)} -> {b : Vect k1 (TDef m)} -> TApp t a = TApp u b -> t = u
tappInjNamed Refl = Refl

tappInjVect : {t : TNamed k} -> {u : TNamed k1} -> {a : Vect k (TDef n)} -> {b : Vect k1 (TDef m)} -> TApp t a = TApp u b -> a = b
tappInjVect Refl = Refl

vectInj : {xs : Vect n a} -> {xs' : Vect m a} -> xs = xs' -> n = m
vectInj Refl = Refl

tnameInjName : {name, name' : String} -> TName name def = TName name' def' -> name = name'
tnameInjName Refl = Refl

tnameInjDef : {def, def' : TDef k} -> TName name def = TName name' def' -> def = def'
tnameInjDef Refl = Refl

-- inequality proofs

t0NotT1 : T0 = T1 -> Void
t0NotT1 Refl impossible

t0NotTSum : T0 = TSum a -> Void
t0NotTSum Refl impossible

t0NotTProd : T0 = TProd a -> Void
t0NotTProd Refl impossible

t0NotTVar : T0 = TVar a -> Void
t0NotTVar Refl impossible

t0NotTMu : T0 = TMu a -> Void
t0NotTMu Refl impossible

t0NotTApp : T0 = TApp n a -> Void
t0NotTApp Refl impossible

t1NotTSum : T1 = TSum a -> Void
t1NotTSum Refl impossible

t1NotTProd : T1 = TProd a -> Void
t1NotTProd Refl impossible

t1NotTVar : T1 = TVar a -> Void
t1NotTVar Refl impossible

t1NotTMu : T1 = TMu a -> Void
t1NotTMu Refl impossible

t1NotTApp : T1 = TApp n a -> Void
t1NotTApp Refl impossible

tSumNotTProd : TSum a = TProd b -> Void
tSumNotTProd Refl impossible

tSumNotTVar : TSum a = TVar b -> Void
tSumNotTVar Refl impossible

tSumNotTMu : TSum a = TMu b -> Void
tSumNotTMu Refl impossible

tSumNotTApp : TSum a = TApp n b -> Void
tSumNotTApp Refl impossible

tProdNotTVar : TProd a = TVar b -> Void
tProdNotTVar Refl impossible

tProdNotTMu : TProd a = TMu b -> Void
tProdNotTMu Refl impossible

tProdNotTApp : TProd a = TApp n b -> Void
tProdNotTApp Refl impossible

tVarNotTMu : TVar a = TMu b -> Void
tVarNotTMu Refl impossible

tVarNotTApp : TVar a = TApp n b -> Void
tVarNotTApp Refl impossible

tMuNotTApp : TMu a = TApp n b -> Void
tMuNotTApp Refl impossible

-- decidable equality proofs

mutual
  DecEq (TDef n) where
    decEq T0              T0                   = Yes Refl
    decEq T1              T1                   = Yes Refl
    decEq (TSum {k} xs)   (TSum {k=k2} xs')    with (decEq k k2)
      decEq (TSum {k} xs) (TSum {k} xs')         | Yes Refl with (assert_total $ decEq xs xs')
        decEq (TSum {k} xs) (TSum {k} xs)          | Yes Refl | Yes Refl = Yes Refl
        decEq (TSum {k} xs) (TSum {k} xs')         | Yes Refl | No ctra = No $ ctra . tsumInj
      decEq (TSum {k} xs) (TSum {k=k2} xs')      | No ctra = No $ ctra . (succInjective _ _) . (succInjective _ _) . vectInj . tsumInj
    decEq (TProd {k} xs)  (TProd {k=k2} xs')   with (decEq k k2)
      decEq (TProd {k} xs) (TProd {k} xs')       | Yes Refl with (assert_total $ decEq xs xs')
        decEq (TProd {k} xs) (TProd {k} xs)        | Yes Refl | Yes Refl = Yes Refl
        decEq (TProd {k} xs) (TProd {k} xs')       | Yes Refl | No ctra = No $ ctra . tprodInj
      decEq (TProd {k} xs) (TProd {k=k2} xs')    | No ctra = No $ ctra . (succInjective _ _) . (succInjective _ _) . vectInj . tprodInj
    decEq (TVar i)        (TVar j)             with (decEq i j)
      decEq (TVar i)        (TVar i)             | Yes Refl = Yes Refl
      decEq (TVar i)        (TVar j)             | No ctra  = No $ ctra . tvarInj
    decEq (TMu {k} xs)    (TMu {k=k2} xs')     with (decEq k k2)
      decEq (TMu {k} xs) (TMu {k} xs')           | Yes Refl with (assert_total $ decEq xs xs')
        decEq (TMu {k} xs) (TMu {k} xs)            | Yes Refl | Yes Refl = Yes Refl
        decEq (TMu {k} xs) (TMu {k} xs')           | Yes Refl | No ctra  = No $ ctra . tmuInj
      decEq (TMu {k} xs) (TMu {k=k2} xs')        | No ctra = No $ ctra . vectInj . tmuInj
    decEq (TApp {k} f xs) (TApp {k=k2} f' xs') with (decEq k k2)
      decEq (TApp {k} f xs) (TApp {k} f' xs')    | Yes Refl with (decEq f f')
        decEq (TApp {k} f xs) (TApp {k} f xs')     | Yes Refl | Yes Refl with (assert_total $ decEq xs xs')
          decEq (TApp {k} f xs) (TApp {k} f xs)      | Yes Refl | Yes Refl | Yes Refl = Yes Refl
          decEq (TApp {k} f xs) (TApp {k} f xs')     | Yes Refl | Yes Refl | No ctra  = No $ ctra . tappInjVect
        decEq (TApp {k} f xs) (TApp {k} f' xs')    | Yes Refl | No ctra  = No $ ctra . tappInjNamed
      decEq (TApp {k} f xs) (TApp {k=k2} f' xs') | No ctra  = No $ ctra . vectInj . tappInjVect
    decEq T0              T1                   = No t0NotT1
    decEq T0              (TSum a)             = No t0NotTSum
    decEq T0              (TProd a)            = No t0NotTProd
    decEq T0              (TVar a)             = No t0NotTVar
    decEq T0              (TMu a)              = No t0NotTMu
    decEq T0              (TApp n a)           = No t0NotTApp
    decEq T1              T0                   = No $ negEqSym t0NotT1
    decEq T1              (TSum a)             = No t1NotTSum
    decEq T1              (TProd a)            = No t1NotTProd
    decEq T1              (TVar a)             = No t1NotTVar
    decEq T1              (TMu a)              = No t1NotTMu
    decEq T1              (TApp n a)           = No t1NotTApp
    decEq (TSum a)        T0                   = No $ negEqSym t0NotTSum
    decEq (TSum a)        T1                   = No $ negEqSym t1NotTSum
    decEq (TSum a)        (TProd b)            = No tSumNotTProd
    decEq (TSum a)        (TVar b)             = No tSumNotTVar
    decEq (TSum a)        (TMu b)              = No tSumNotTMu
    decEq (TSum a)        (TApp n b)           = No tSumNotTApp
    decEq (TProd a)       T0                   = No $ negEqSym t0NotTProd
    decEq (TProd a)       T1                   = No $ negEqSym t1NotTProd
    decEq (TProd a)       (TSum b)             = No $ negEqSym tSumNotTProd
    decEq (TProd a)       (TVar b)             = No tProdNotTVar
    decEq (TProd a)       (TMu b)              = No tProdNotTMu
    decEq (TProd a)       (TApp n b)           = No tProdNotTApp
    decEq (TVar i)        T0                   = No $ negEqSym t0NotTVar
    decEq (TVar i)        T1                   = No $ negEqSym t1NotTVar
    decEq (TVar i)        (TSum b)             = No $ negEqSym tSumNotTVar
    decEq (TVar i)        (TProd b)            = No $ negEqSym tProdNotTVar
    decEq (TVar i)        (TMu b)              = No tVarNotTMu
    decEq (TVar i)        (TApp n b)           = No tVarNotTApp
    decEq (TMu a)         T0                   = No $ negEqSym t0NotTMu
    decEq (TMu a)         T1                   = No $ negEqSym t1NotTMu
    decEq (TMu a)         (TSum b)             = No $ negEqSym tSumNotTMu
    decEq (TMu a)         (TProd b)            = No $ negEqSym tProdNotTMu
    decEq (TMu a)         (TVar i)             = No $ negEqSym tVarNotTMu
    decEq (TMu a)         (TApp n b)           = No tMuNotTApp
    decEq (TApp n a)      T0                   = No $ negEqSym t0NotTApp
    decEq (TApp n a)      T1                   = No $ negEqSym t1NotTApp
    decEq (TApp n a)      (TSum b)             = No $ negEqSym tSumNotTApp
    decEq (TApp n a)      (TProd b)            = No $ negEqSym tProdNotTApp
    decEq (TApp n a)      (TVar i)             = No $ negEqSym tVarNotTApp
    decEq (TApp n a)      (TMu b)              = No $ negEqSym tMuNotTApp

  DecEq (TNamed n) where
    decEq (TName name def) (TName name' def') with (decEq name name')
      decEq (TName name def) (TName name def')  | Yes Refl with (decEq def def')
        decEq (TName name def) (TName name def)   | Yes Refl | Yes Refl = Yes Refl
        decEq (TName name def) (TName name def')  | Yes Refl | No ctra = No $ ctra . tnameInjDef
      decEq (TName name def) (TName name' def') | No ctra  = No $ ctra . tnameInjName
