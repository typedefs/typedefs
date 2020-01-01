module Typedefs.Syntax.Compiler

import Data.Vect
import Data.NEList

import Effects
import Effect.Exception
import Effect.State

import Typedefs.Typedefs
import Typedefs.Syntax.AST
import Typedefs.Names
import Typedefs.Backend.Utils
import Typedefs.Parse

%default total

natMax : Nat -> Nat -> Nat
natMax Z n = n
natMax n Z = n
natMax (S k) (S l) = S (natMax k l)

natMaxSym : (a, b : Nat) -> natMax a b = natMax b a
natMaxSym Z Z = Refl
natMaxSym Z (S k) = Refl
natMaxSym (S k) Z = Refl
natMaxSym (S k) (S j) = cong $ natMaxSym k j

natMaxSucc : (a, b : Nat) -> natMax (S a) (S b) = S (natMax a b)
natMaxSucc Z Z = Refl
natMaxSucc Z (S k) = Refl
natMaxSucc (S k) Z = Refl
natMaxSucc (S k) (S j) = cong $ natMaxSucc k j

magicProof : (n, m : Nat) -> n `LTE` (natMax n m)
magicProof Z _ = LTEZero
magicProof Z (S k) = LTEZero
magicProof (S k) Z = lteRefl
magicProof (S k) (S j) = LTESucc $ magicProof k j

weakenMax : (n, m : Nat) -> TDef n -> (TDef (natMax n m))
weakenMax n m tdef = weakenTDef tdef (natMax n m) (magicProof n m)

||| Same a weakenMax but symetric
weakenMax' : (n, m : Nat) -> TDef m -> (TDef (natMax n m))
weakenMax' n m tdef = rewrite natMaxSym n m in weakenMax m n tdef

CompilerM : Type -> Type
CompilerM t = Eff t [EXCEPTION String]

fromNat : Nat -> TDef n
fromNat Z = T0
fromNat (S Z) = T1
fromNat (S (S n)) = TSum (replicate (S (S n)) T1)

makeElem : {e : String} -> Data.List.Elem e ls -> TDef (length ls)
makeElem Here = TVar FZ
makeElem (There later) = shiftVars $ makeElem later

findList : String -> (ls : List String) -> TDef (length ls)
findList name ls with (name `isElem` ls)
  | Yes elem = makeElem elem
  | No nope = FRef name


mutual
  compilePower : (names : List String) -> AST.Power -> CompilerM (Either Nat (TDef (length names)))
  compilePower names (PLit n) = pure (Left n)
  compilePower names (PEmb x) = pure (Right !(compileExpr names x))

  compileFactor : (names : List String) -> AST.Factor -> CompilerM (TDef (length names))
  compileFactor names (FEmb x) = do Left n <- compilePower names x
                                      | Right def => pure def
                                    pure (fromNat n)
  compileFactor names (FPow x y) = do
    f <- compileFactor names x
    case !(compilePower names y) of
         Left p => pure $ (Typedefs.pow p f)
         Right def => pure def

  compileTerm : (names : List String) -> AST.Term -> CompilerM (TDef (length names))
  compileTerm names (TEmb x) = compileFactor names x
  compileTerm names (TMul x y) = do t <- compileTerm names x
                                    f <- compileFactor names y
                                    pure $ (TProd [t, f])

  compileExpr : (names : List String) -> AST.Expr -> CompilerM (TDef (length names))
  compileExpr names (EEmb x) = compileTerm names x
  compileExpr names (ESum x y) = do e <- compileExpr names x
                                    t <- compileTerm names y
                                    pure $ TSum [e, t]
  compileExpr names (Ref x) = pure $ findList x names
  compileExpr names (EApp n args) = do
    compiledArgs <- traverseEffect (assert_total $ compileExpr names) $ toVect args
    pure $ TApp (TName n (FRef n)) compiledArgs

plusSuccSucc : (li, ri : Nat) -> plus (S li) (S ri) = S (S (plus li ri))
plusSuccSucc li ri = cong {f=S} $ sym $ plusSuccRightSucc li ri

flattenSum : TDef Z -> (n ** Vect (S n) (TDef Z))
flattenSum (TSum [l, r]) = let (li ** left) = flattenSum l
                               (ri ** right) = flattenSum r
                               vect = (left ++ right)
                            in (li + (S ri) ** vect)
flattenSum tdef = (Z ** [tdef])

flattenMult : TDef Z -> (n ** Vect (S n) (TDef Z))
flattenMult (TProd [l, r]) = let (li ** left) = flattenMult l
                                 (ri ** right) = flattenMult r
                              in (li + (S ri) ** (left ++ right))
flattenMult tdef = (Z ** [tdef])

flattenExpressionTree : TDef Z -> TDef Z
flattenExpressionTree (TSum [l, r]) =
  let (li ** left) = flattenSum l
      (ri ** right) = flattenSum r
      plusProof = cong {f=S} $ sym $ plusSuccRightSucc li ri
      prf = cong {f = \x => Vect x (TDef Z)} $ plusProof
      prd2 = replace {P=id} prf (left ++ right)
   in TSum prd2
flattenExpressionTree (TProd [l, r]) =
  let (li ** left) = flattenMult l
      (ri ** right) = flattenMult r
      prf = cong {f = \x => Vect x (TDef Z)} $ plusSuccSucc li ri
      prd2 = replace {P=id} prf (left ++ right)
   in TProd prd2
flattenExpressionTree tdef = tdef

ComputeEffect : {a : Nat -> Type} -> (n ** a n) -> List EFFECT
ComputeEffect (l ** _) = [EXCEPTION String, STATE (Vect l String)]

succPlus : (n : Nat) -> S n = n + 1
succPlus Z = Refl
succPlus (S k) = cong {f=S} $ succPlus k

trivialLTE : (m : Nat) -> m `LTE` (S m)
trivialLTE Z = LTEZero
trivialLTE (S k) = LTESucc (trivialLTE k)

isVarList : Vect k (TDef n) -> Bool
isVarList vs = isVarList' vs Z
  where
    isVarList' : Vect k (TDef n) -> Nat -> Bool
    isVarList' (TVar var :: xs) fin = if toNat var == fin then isVarList' xs (S fin)
                                                          else False
    isVarList' [] _ = True
    isVarList' _ _ = False

isRefName : String -> TNamed n -> Bool
isRefName n (TName name (FRef rn)) = n == name && rn == n
isRefName _ _ = False

-- Replace all uses of self application with "__self__"
findRef : String -> TDef i -> TDef i
findRef x T0 = T0
findRef x T1 = T1
findRef x (TSum ys) = TSum $ map (assert_total $ findRef x) ys
findRef x (TProd ys) = TProd $ map (assert_total $ findRef x) ys
findRef x (TVar n) = TVar n
findRef x (TMu ys) = TMu $ map (map $ assert_total (findRef x)) ys
findRef n (TApp ndef defs) = if isRefName n ndef && isVarList defs
  then FRef "__self__" -- we python now
  else TApp ndef $ map (assert_total $ findRef n) defs
findRef x (FRef y) = FRef y

-- replace all occurences of "__self__" with (TVar FZ)
replaceRef : String -> TDef (S i) -> TDef (S i)
replaceRef x T0 = T0
replaceRef x T1 = T1
replaceRef x (TSum ys) = TSum $ map (assert_total $ replaceRef x) ys
replaceRef x (TProd ys) = TProd $ map (assert_total $ replaceRef x) ys
replaceRef x (TVar n) = TVar n
replaceRef x (TMu ys) = TMu $ map (map $ assert_total (replaceRef x)) ys
replaceRef n (TApp ndef defs) =
  TApp ndef $ map (assert_total $ replaceRef n) defs
replaceRef x (FRef y) = if y == "__self__" then TVar FZ else FRef y

||| Given a name and a vector of TDef, replace references pointing to the name with `Var 0`
||| This also either weakens or increments all references
findRecusion : String -> List String -> Vect n (TDef i) -> Vect n (TDef (S i))
findRecusion name args defs = map findRec defs
  where
    findRec : TDef i -> TDef (S i)
    findRec def = let self = findRef name def
                      shifted = shiftVars self
                   in replaceRef name shifted

checkDefs : Vect n a -> CompilerM (k ** Vect (2 + k) a)
checkDefs [x, y] = pure (Z ** [x, y])
checkDefs (x :: xs) = do (n ** ns) <- checkDefs xs
                         pure (S n ** x :: ns)
checkDefs _ = raise "enum doesn't have at least two constructors"

||| Compile an enum syntax down to a TMu
||| @name the name given to the type
||| @args the names used as type parameters
||| @constructors the list of constructors for each value
compileEnum : (name : String) -> (args : List String)
           -> (constructors : Vect m (String, TDef (length args)))
           -> CompilerM (n ** TNamed n)
compileEnum name args constructors = do
  (k ** checkedDefs) <- checkDefs constructors
  let recursed = findRecusion name args (map snd checkedDefs)
  let pairs = zip (map fst checkedDefs) recursed
  pure (length args ** TName name (TMu pairs))

compileDef : AST.TopLevelDef -> CompilerM (n ** TNamed n)
compileDef (MkTopLevelDef (MkDefName defn args) (Simple x)) = do
  c <- compileExpr args x
  pure (List.length args ** TName defn c)
compileDef (MkTopLevelDef (MkDefName n args) (Enum xs)) = do
  exprdef <- traverseEffect (\(n, d) => MkPair n <$> (compileExpr args d)) (fromList xs)
  compileEnum n args exprdef
compileDef (MkTopLevelDef def (Record xs)) = raise "records are not supported at this time"


export
compileEither : AST.TopLevelDef -> Either String (n ** TNamed n)
compileEither ast = run (compileDef ast)

listDef : AST.TopLevelDef
listDef = MkTopLevelDef (MkDefName "List" ["a"])
  (Enum [ ("Nil", EEmb $ TEmb $ FEmb $ PLit 1)
        , ("Cons", EEmb $ TMul (TEmb $ FEmb $ PEmb $ Ref "a")
                                      (FEmb $ PEmb $ EApp "List" (MkNEList (Ref "a") [])))])
