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

trefInj : (FRef r = FRef r') -> r = r'
trefInj Refl = Refl

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

t0NotRRef : T0 = RRef r -> Void
t0NotRRef Refl impossible

t0NotFRef : T0 = FRef r -> Void
t0NotFRef Refl impossible

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

t1NotRRef : T1 = RRef r -> Void
t1NotRRef Refl impossible

t1NotFRef : T1 = FRef r -> Void
t1NotFRef Refl impossible

tSumNotTProd : TSum a = TProd b -> Void
tSumNotTProd Refl impossible

tSumNotTVar : TSum a = TVar b -> Void
tSumNotTVar Refl impossible

tSumNotTMu : TSum a = TMu b -> Void
tSumNotTMu Refl impossible

tSumNotTApp : TSum a = TApp n b -> Void
tSumNotTApp Refl impossible

tSumNotRRef : TSum a = RRef r -> Void
tSumNotRRef Refl impossible

tSumNotFRef : TSum a = FRef r -> Void
tSumNotFRef Refl impossible

tProdNotTVar : TProd a = TVar b -> Void
tProdNotTVar Refl impossible

tProdNotTMu : TProd a = TMu b -> Void
tProdNotTMu Refl impossible

tProdNotTApp : TProd a = TApp n b -> Void
tProdNotTApp Refl impossible

tProdNotRRef : TProd a = RRef r -> Void
tProdNotRRef Refl impossible

tProdNotFRef : TProd a = FRef r -> Void
tProdNotFRef Refl impossible

tVarNotTMu : TVar a = TMu b -> Void
tVarNotTMu Refl impossible

tVarNotTApp : TVar a = TApp n b -> Void
tVarNotTApp Refl impossible

tVarNotRRef : TVar a = RRef r -> Void
tVarNotRRef Refl impossible

tVarNotFRef : TVar a = FRef r -> Void
tVarNotFRef Refl impossible

tMuNotTApp : TMu a = TApp n b -> Void
tMuNotTApp Refl impossible

tMuNotRRef : TMu a = RRef r -> Void
tMuNotRRef Refl impossible

tMuNotFRef : TMu a = FRef r -> Void
tMuNotFRef Refl impossible

tAppNotRRef : TApp n t = RRef r -> Void
tAppNotRRef Refl impossible

tAppNotFRef : TApp n t = FRef r -> Void
tAppNotFRef Refl impossible

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
    decEq (FRef r)        (FRef r')            with (decEq r r')
      decEq (FRef r)        (FRef r)             | (Yes Refl) = Yes Refl
      decEq (FRef r)        (FRef r')            | (No ctra) = No $ ctra . trefInj
    decEq T0              T1                   = No t0NotT1
    decEq T0              (TSum xs)            = No t0NotTSum
    decEq T0              (TProd xs)           = No t0NotTProd
    decEq T0              (TVar i)             = No t0NotTVar
    decEq T0              (TMu xs)             = No t0NotTMu
    decEq T0              (TApp x xs)          = No t0NotTApp
    decEq T0              (FRef _)             = No t0NotFRef
    decEq T1              T0                   = No $ negEqSym t0NotT1
    decEq T1              (TSum xs)            = No t1NotTSum
    decEq T1              (TProd xs)           = No t1NotTProd
    decEq T1              (TVar i)             = No t1NotTVar
    decEq T1              (TMu xs)             = No t1NotTMu
    decEq T1              (TApp x xs)          = No t1NotTApp
    decEq T1              (FRef x)             = No t1NotFRef
    decEq (TSum xs)       T0                   = No $ negEqSym t0NotTSum
    decEq (TSum xs)       T1                   = No $ negEqSym t1NotTSum
    decEq (TSum xs)       (TProd ys)           = No tSumNotTProd
    decEq (TSum xs)       (TVar i)             = No tSumNotTVar
    decEq (TSum xs)       (TMu ys)             = No tSumNotTMu
    decEq (TSum xs)       (TApp x ys)          = No tSumNotTApp
    decEq (TSum xs)       (FRef x)             = No tSumNotFRef
    decEq (TProd xs)      T0                   = No $ negEqSym t0NotTProd
    decEq (TProd xs)      T1                   = No $ negEqSym t1NotTProd
    decEq (TProd xs)      (TSum ys)            = No $ negEqSym tSumNotTProd
    decEq (TProd xs)      (TVar i)             = No tProdNotTVar
    decEq (TProd xs)      (TMu ys)             = No tProdNotTMu
    decEq (TProd xs)      (TApp x ys)          = No tProdNotTApp
    decEq (TProd xs)      (FRef x)             = No tProdNotFRef
    decEq (TVar i)        T0                   = No $ negEqSym t0NotTVar
    decEq (TVar i)        T1                   = No $ negEqSym t1NotTVar
    decEq (TVar i)        (TSum xs)            = No $ negEqSym tSumNotTVar
    decEq (TVar i)        (TProd xs)           = No $ negEqSym tProdNotTVar
    decEq (TVar i)        (TMu xs)             = No tVarNotTMu
    decEq (TVar i)        (TApp x xs)          = No tVarNotTApp
    decEq (TVar i)        (FRef x)             = No tVarNotFRef
    decEq (TMu xs)        T0                   = No $ negEqSym t0NotTMu
    decEq (TMu xs)        T1                   = No $ negEqSym t1NotTMu
    decEq (TMu xs)        (TSum ys)            = No $ negEqSym tSumNotTMu
    decEq (TMu xs)        (TProd ys)           = No $ negEqSym tProdNotTMu
    decEq (TMu xs)        (TVar i)             = No $ negEqSym tVarNotTMu
    decEq (TMu xs)        (TApp x ys)          = No tMuNotTApp
    decEq (TMu xs)        (FRef x)             = No tMuNotFRef
    decEq (TApp x xs)     T0                   = No $ negEqSym t0NotTApp
    decEq (TApp x xs)     T1                   = No $ negEqSym t1NotTApp
    decEq (TApp x xs)     (TSum ys)            = No $ negEqSym tSumNotTApp
    decEq (TApp x xs)     (TProd ys)           = No $ negEqSym tProdNotTApp
    decEq (TApp x xs)     (TVar i)             = No $ negEqSym tVarNotTApp
    decEq (TApp x xs)     (TMu ys)             = No $ negEqSym tMuNotTApp
    decEq (TApp x xs)     (FRef y)             = No tAppNotFRef
    decEq (FRef x)      T0                     = No $ negEqSym t0NotFRef
    decEq (FRef x)      T1                     = No $ negEqSym t1NotFRef
    decEq (FRef x)      (TSum xs)              = No $ negEqSym tSumNotFRef
    decEq (FRef x)      (TProd xs)             = No $ negEqSym tProdNotFRef
    decEq (FRef x)      (TVar i)               = No $ negEqSym tVarNotFRef
    decEq (FRef x)      (TMu xs)               = No $ negEqSym tMuNotFRef
    decEq (FRef x)      (TApp y xs)            = No $ negEqSym tAppNotFRef
    decEq _ _ = No $ believe_me

  DecEq (TNamed n) where
    decEq (TName name def) (TName name' def') with (decEq name name')
      decEq (TName name def) (TName name def')  | Yes Refl with (decEq def def')
        decEq (TName name def) (TName name def)   | Yes Refl | Yes Refl = Yes Refl
        decEq (TName name def) (TName name def')  | Yes Refl | No ctra = No $ ctra . tnameInjDef
      decEq (TName name def) (TName name' def') | No ctra  = No $ ctra . tnameInjName
