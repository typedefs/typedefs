module TypedefsDecEq

import Decidable.Equality
import Data.Vect
import Data.Nat
import Typedefs

%default total

-- injectivity proofs

tsumInjLen : {xs : Vect (2+k1) (TDef' n b)} ->
             {ys : Vect (2+k2) (TDef' n b)} ->
             TSum xs = TSum ys -> k1 = k2
tsumInjLen Refl = Refl

tprodInjLen : {xs : Vect (2+k1) (TDef' n b)} ->
              {ys : Vect (2+k2) (TDef' n b)} ->
              TProd xs = TProd ys -> k1 = k2
tprodInjLen Refl = Refl

tmuInjLen : {xs : Vect k1 (String, TDef' (S n) b)} ->
            {ys : Vect k2 (String, TDef' (S n) b)} ->
            TMu xs = TMu ys -> k1 = k2
tmuInjLen Refl = Refl

interface Injective (i : a -> b) where
  inj : (i x = i y) -> x = y

Injective RRef where
  inj Refl = Refl

Injective FRef where
  inj Refl = Refl

Injective TMu where
  inj Refl = Refl

Injective TSum where
  inj Refl = Refl

Injective TProd where
  inj Refl = Refl

Injective TVar where
  inj Refl = Refl

vectTailInj : {0 xs, ys : Vect n a} -> x :: xs = x :: ys -> xs = ys
vectTailInj Refl = Refl

vectHeadInj : {0 xs, ys : Vect n a} -> x :: xs = y :: ys -> x = y
vectHeadInj Refl = Refl

vectLenInjSS : {xs : Vect (S (S k1)) a} ->
               {ys : Vect (S (S k2)) a} ->
               xs = ys -> k1 = k2
vectLenInjSS Refl = Refl

vectLenInj : {xs : Vect k1 a} ->
             {ys : Vect k2 a} ->
             xs = ys -> k1 = k2
vectLenInj Refl = Refl

export
tmuInj : {a : Vect k1 (String, TDef' (S n) v)} -> {b : Vect k2 (String, TDef' (S m) v)} -> TMu a = TMu b -> a = b
tmuInj Refl = Refl

tappInjNamed : {t : TNamed' k b} -> {u : TNamed' k1 b} -> {a : Vect k (TDef' n b)} ->
               {c : Vect k1 (TDef' m b)} -> TApp t a = TApp u c -> t = u
tappInjNamed Refl = Refl

tappInjVect : {t : TNamed' k b} -> {u : TNamed' k1 b} -> {a : Vect k (TDef' n b)} ->
              {c : Vect k1 (TDef' m b)} -> TApp t a = TApp u c -> a = c
tappInjVect Refl = Refl

tnameInjName : {name, name' : String} -> TName name def = TName name' def' -> name = name'
tnameInjName Refl = Refl

tnameInjDef : {def, def' : TDef' k b} -> TName name def = TName name' def' -> def = def'
tnameInjDef Refl = Refl

frefInj : (FRef r = FRef r') -> r = r'
frefInj Refl = Refl

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

tAppNotRRef : (TApp n t = RRef r) -> Void
tAppNotRRef Refl impossible

tapp_not_fref : TApp n t = FRef r -> Void
tapp_not_fref Refl impossible

sym' : (x = y) -> y = x
sym' Refl = Refl

-- decidable equality proofs

injContra : {xs : Vect (2+k1) (TDef' n b)} ->
            {ys : Vect (2+k2) (TDef' n b)} ->
            (k1 = k2 -> Void) ->
            TSum xs = TSum ys -> Void
injContra ctr prf = ctr $ tsumInjLen prf

mutual
  [vectTDef] DecEq (Vect n (TDef' n v)) where
    decEq [] [] = Yes Refl
    decEq (x :: xs) (y :: ys) with (decEq x y)
      decEq (x :: xs) (x :: ys) | (Yes Refl) with (decEq xs ys)
        decEq (x :: ys) (x :: ys) | (Yes Refl) | (Yes Refl) = Yes Refl
        decEq (x :: xs) (x :: ys) | (Yes Refl) | (No contra) = No $ contra . vectTailInj
      decEq (x :: xs) (y :: ys) | (No contra) = No $ contra . vectHeadInj

  public export
  DecEq (TDef' n v) where
    decEq T0 {n = n} T0 = Yes Refl
    decEq T1 {n = n} T1 = Yes Refl
    decEq T0 {n = n} T1 = No t0NotT1
    decEq T0 {n = n} (TSum xs) = No t0NotTSum
    decEq T0 {n = n} (TProd xs) = No t0NotTProd
    decEq T0 {n = (S n)} (TVar i) = No t0NotTVar
    decEq T0 {n = n} (TMu xs) = No t0NotTMu
    decEq T0 {n = n} (TApp x xs) = No t0NotTApp
    decEq T0 {n = (S n)} (RRef x) = No t0NotRRef
    decEq T0 {n = n} (FRef x) = No t0NotFRef
    decEq T1 {n = n} T0 = No $ t0NotT1 . sym'
    decEq T1 {n = n} (TSum xs) = No t1NotTSum
    decEq T1 {n = n} (TProd xs) = No t1NotTProd
    decEq T1 {n = (S n)} (TVar i) = No t1NotTVar
    decEq T1 {n = n} (TMu xs) = No t1NotTMu
    decEq T1 {n = n} (TApp x xs) = No t1NotTApp
    decEq T1 {n = (S n)} (RRef x) = No t1NotRRef
    decEq T1 {n = n} (FRef x) = No t1NotFRef
    decEq (TSum xs) T0 = No $ t0NotTSum . sym'
    decEq (TSum xs) T1 = No $ t1NotTSum . sym'
    decEq (TSum {k=k1} xs) (TSum {k=k2} ys) with (decEq k1 k2)
      decEq (TSum {k = k1} xs) (TSum {k = k1} ys) | (Yes Refl) with (assert_total $ decEq xs ys)
        decEq (TSum {k = k1} xs) (TSum {k = k1} ys) | (Yes Refl) | (Yes prf) = Yes $ cong TSum prf
        decEq (TSum {k = k1} xs) (TSum {k = k1} ys) | (Yes Refl) | (No contra) = No $ contra . inj
      decEq (TSum {k = k1} xs) (TSum {k = k2} ys) | (No contra) = No $ injContra contra
    decEq (TSum xs) (TProd ys) = No tSumNotTProd
    decEq (TSum xs) (TVar i) = No tSumNotTVar
    decEq (TSum xs) (TMu ys) = No tSumNotTMu
    decEq (TSum xs) (TApp x ys) = No tSumNotTApp
    decEq (TSum xs) (RRef x) = No tSumNotRRef
    decEq (TSum xs) (FRef x) = No tSumNotFRef
    decEq (TProd xs) T0 = No $ t0NotTProd . sym'
    decEq (TProd xs) T1 = No $ t1NotTProd . sym'
    decEq (TProd xs) (TSum ys) = No $ tSumNotTProd . sym'
    decEq (TProd {k=k1} xs) (TProd {k=k2} ys) with (decEq k1 k2)
      decEq (TProd {k=k1} xs) (TProd {k=k1} ys) | (Yes Refl) with (assert_total $ decEq xs ys)
        decEq (TProd {k = k1} xs) (TProd {k = k1} ys) | (Yes Refl) | (Yes prf) = Yes $ cong TProd prf
        decEq (TProd {k = k1} xs) (TProd {k = k1} ys) | (Yes Refl) | (No contra) = No $ contra . inj
      decEq (TProd {k=k1} xs) (TProd {k=k2} ys) | (No contra) = No $ contra . tprodInjLen
    decEq (TProd xs) (TVar i) = No tProdNotTVar
    decEq (TProd xs) (TMu ys) = No tProdNotTMu
    decEq (TProd xs) (TApp x ys) = No tProdNotTApp
    decEq (TProd xs) (RRef x) = No tProdNotRRef
    decEq (TProd xs) (FRef x) = No tProdNotFRef
    decEq (TVar i) T0 = No $ t0NotTVar . sym'
    decEq (TVar i) T1 = No $ t1NotTVar . sym'
    decEq (TVar i) (TSum xs) = No $ tSumNotTVar . sym'
    decEq (TVar i) (TProd xs) = No $ tProdNotTVar . sym'
    decEq (TVar i) (TVar x) with (decEq i x)
      decEq (TVar i) (TVar x) | (Yes prf) = Yes $ cong TVar prf
      decEq (TVar i) (TVar x) | (No contra) = No $ contra . inj
    decEq (TVar i) (TMu xs) = No tVarNotTMu
    decEq (TVar i) (TApp x xs) = No tVarNotTApp
    decEq (TVar i) (RRef x) = No tVarNotRRef
    decEq (TVar i) (FRef x) = No tVarNotFRef
    decEq (TMu {k=k1} xs) T0 = No $ t0NotTMu . sym'
    decEq (TMu {k=k1} xs) T1 = No $ t1NotTMu . sym'
    decEq (TMu {k=k1} xs) (TSum ys) = No $ tSumNotTMu . sym'
    decEq (TMu {k=k1} xs) (TProd ys) = No $ tProdNotTMu . sym'
    decEq (TMu {k=k1} xs) (TVar i) = No $ tVarNotTMu . sym'
    decEq (TMu {k=k1} xs) (TMu {k=k2} ys) with (decEq k1 k2)
      decEq (TMu {k = k1} xs) (TMu {k = k1} ys) | (Yes Refl) with (assert_total $ decEq xs ys)
        decEq (TMu {  k = k1} xs) (TMu {  k = k1} ys) | (Yes Refl) | (Yes prf) = Yes $ cong TMu prf
        decEq (TMu {  k = k1} xs) (TMu {  k = k1} ys) | (Yes Refl) | (No contra) = No $ contra . inj
      decEq (TMu {k = k1} xs) (TMu {k = k2} ys) | (No contra) = No $ contra . tmuInjLen
    decEq (TMu {k=k1} xs) (TApp x ys) = No tMuNotTApp
    decEq (TMu {k=k1} xs) (RRef x) = No tMuNotRRef
    decEq (TMu {k=k1} xs) (FRef x) = No tMuNotFRef
    decEq (TApp x xs) T0 = No $ t0NotTApp . sym'
    decEq (TApp x xs) T1 = No $ t1NotTApp . sym'
    decEq (TApp x xs) (TSum ys) = No $ tSumNotTApp . sym'
    decEq (TApp x xs) (TProd ys) = No $ tProdNotTApp . sym'
    decEq (TApp x xs) (TVar i) = No $ tVarNotTApp . sym'
    decEq (TApp x xs) (TMu ys) = No $ tMuNotTApp . sym'
    decEq (TApp {k=k1} x xs) (TApp {k=k2} y ys) with (decEq k1 k2)
      decEq (TApp {k=k1} x xs) (TApp {k=k1} y ys) | (Yes Refl) with (assert_total $ decEq x y)
        decEq (TApp {k = k1} x xs) (TApp {k = k1} y ys) | (Yes Refl) | (Yes prf)
          with (assert_total $ decEq xs ys)
          decEq (TApp {k = k1} x xs) (TApp {k = k1} y ys) | (Yes Refl) | (Yes prf) | (Yes prf2) =
            Yes $ rewrite prf in rewrite prf2 in Refl
          decEq (TApp {k = k1} x xs) (TApp {k = k1} y ys) | (Yes Refl) | (Yes prf) | (No contra) =
            No $ rewrite prf in contra . tappInjVect
        decEq (TApp {k = k1} x xs) (TApp {k = k1} y ys) | (Yes Refl) | (No contra) =
          No $ contra . tappInjNamed
      decEq (TApp {k=k1} x xs) (TApp {k=k2} y ys) | (No contra) =
        No $ contra . vectLenInj . tappInjVect
    decEq (TApp x xs) (RRef r) = No tAppNotRRef
    decEq (TApp x xs) (FRef r) = No tapp_not_fref
    decEq (RRef x) T0 = No $ t0NotRRef . sym'
    decEq (RRef x) T1 = No $ t1NotRRef . sym'
    decEq (RRef x) (TSum xs) = No $ tSumNotRRef . sym'
    decEq (RRef x) (TProd xs) = No $ tProdNotRRef . sym'
    decEq (RRef x) (TVar i) = No $ tVarNotRRef . sym'
    decEq (RRef x) (TMu xs) = No $ tMuNotRRef . sym'
    decEq (RRef x) (TApp y xs) = No $ tAppNotRRef . sym'
    decEq (RRef x) (RRef y) with (decEq x y)
      decEq (RRef x) (RRef y) | (Yes prf) = Yes $ cong RRef prf
      decEq (RRef x) (RRef y) | (No contra) = No $ contra . inj
    decEq (FRef x) T0 = No $ t0NotFRef . sym'
    decEq (FRef x) T1 = No $ t1NotFRef . sym'
    decEq (FRef x) (TSum xs) = No $ tSumNotFRef . sym'
    decEq (FRef x) (TProd xs) = No $ tProdNotFRef . sym'
    decEq (FRef x) (TVar i) = No $ tVarNotFRef . sym'
    decEq (FRef x) (TMu xs) = No $ tMuNotFRef . sym'
    decEq (FRef x) (TApp y xs) = No $ tapp_not_fref . sym'
    decEq (FRef x) (FRef y) with (decEq x y)
      decEq (FRef x) (FRef y) | (Yes prf) = Yes $ cong FRef prf
      decEq (FRef x) (FRef y) | (No contra) = No $ contra . inj

  export
  (n : Nat) => DecEq (TNamed' n b) where
    decEq (TName name def) (TName name' def') with (decEq name name')
      decEq (TName name def) (TName name def')  | Yes Refl with (decEq def def')
        decEq (TName name def) (TName name def)   | Yes Refl | Yes Refl = Yes Refl
        decEq (TName name def) (TName name def')  | Yes Refl | No ctra = No $ ctra . tnameInjDef
      decEq (TName name def) (TName name' def') | No ctra  = No $ ctra . tnameInjName
