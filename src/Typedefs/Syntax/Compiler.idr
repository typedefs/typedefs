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

CompilerM : Type -> Type
CompilerM t = Eff t [EXCEPTION String]

ComputeEffect : {a : Nat -> Type} -> (n ** a n) -> List EFFECT
ComputeEffect (l ** _) = [EXCEPTION String, STATE (Vect l String)]

-- convert a Nat into a sum of T1s
fromNat : Nat -> TDef n
fromNat Z = T0
fromNat (S Z) = T1
fromNat (S (S n)) = TSum (replicate (S (S n)) T1)

-- Given a proof than an element is in the list, make a TVar with its index in the list
makeElem : {e : String} -> Data.List.Elem e ls -> TDef (length ls)
makeElem Here = TVar FZ
makeElem (There later) = shiftVars $ makeElem later

-- If the string is an element in the list, make a TVar out of it otherwise return a ref
findList : String -> (ls : List String) -> TDef (length ls)
findList name ls with (name `isElem` ls)
  | Yes elem = makeElem elem
  | No nope = FRef name

mutual
  compilePower : (names : List String) -> AST.Power -> CompilerM (Either Nat (TDef (length names)))
  compilePower names (PLit n) = pure (Left n)
  compilePower names (PEmb x) = pure (Right !(compileAppli names x))
  compilePower names (PRef x) = pure (Right $ findList x names)

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

  compileAppli : (names : List String) -> AST.Appli -> CompilerM (TDef (length names))
  compileAppli names (AEmb x) = compileExpr names x
  compileAppli names (App n args) = do
    compiledArgs <- traverseEffect (assert_total $ compileExpr names) $ toVect args
    pure $ TApp (TName n (FRef n)) compiledArgs

-- Flattening of expression trees, 1 + (1 + 1) are flattened as (+ 1 1 1)

plusSuccSucc : (li, ri : Nat) -> plus (S li) (S ri) = S (S (plus li ri))
plusSuccSucc li ri = cong {f=S} $ sym $ plusSuccRightSucc li ri

flattenExpr : TDef n -> (m ** Vect (S m) (TDef n))
flattenExpr (TSum [l, r]) = let (li ** left) = flattenExpr l
                                (ri ** right) = flattenExpr r
                                vect = (left ++ right)
                            in (li + (S ri) ** vect)
flattenExpr (TProd [l, r]) = let (li ** left) = flattenExpr l
                                 (ri ** right) = flattenExpr r
                              in (li + (S ri) ** (left ++ right))
flattenExpr tdef = (Z ** [tdef])

flattenExpressionTree : TDef n -> TDef n
flattenExpressionTree (TSum [l, r]) {n} =
  let (li ** left) = flattenExpr l
      (ri ** right) = flattenExpr r
      plusProof = cong {f=S} $ sym $ plusSuccRightSucc li ri
      prf = cong {f = \x => Vect x (TDef n)} $ plusProof
      prd2 = replace {P=id} prf (left ++ right)
   in TSum prd2
flattenExpressionTree (TProd [l, r]) {n} =
  let (li ** left) = flattenExpr l
      (ri ** right) = flattenExpr r
      prf = cong {f = \x => Vect x (TDef n)} $ plusSuccSucc li ri
      prd2 = replace {P=id} prf (left ++ right)
   in TProd prd2
flattenExpressionTree tdef = tdef

-- check if a list of TDef is made of TVars of increasing index
isVarList : Vect k (TDef n) -> Bool
isVarList vs = isVarList' vs Z
  where
    isVarList' : Vect k (TDef n) -> Nat -> Bool
    isVarList' (TVar var :: xs) idx = if toNat var == idx then isVarList' xs (S idx)
                                                          else False
    isVarList' [] _ = True
    isVarList' _ _ = False

isRefName : String -> TNamed n -> Bool
isRefName n (TName name (FRef rn)) = n == name && rn == n
isRefName _ _ = False

-- The next three functions could probably be asbtracted somehow

-- Replace all uses of self application with "__self__"
findSelfApp : String -> TDef i -> TDef i
findSelfApp x T0 = T0
findSelfApp x T1 = T1
findSelfApp x (TSum ys) = TSum $ map (assert_total $ findSelfApp x) ys
findSelfApp x (TProd ys) = TProd $ map (assert_total $ findSelfApp x) ys
findSelfApp x (TVar n) = TVar n
findSelfApp x (TMu ys) = TMu $ map (map $ assert_total (findSelfApp x)) ys
findSelfApp n (TApp ndef defs) = if isRefName n ndef && isVarList defs
  then FRef "__self__" -- we python now
  else TApp ndef $ map (assert_total $ findSelfApp n) defs
findSelfApp x (FRef y) = FRef y

findSelfVar : String -> TDef i -> TDef i
findSelfVar x T0 = T0
findSelfVar x T1 = T1
findSelfVar x (TSum ys) = TSum $ map (assert_total $ findSelfVar x) ys
findSelfVar x (TProd ys) = TProd $ map (assert_total $ findSelfVar x) ys
findSelfVar x (TVar n) = TVar n
findSelfVar x (TMu ys) = TMu $ map (map $ assert_total (findSelfVar x)) ys
findSelfVar x (TApp ndef defs) =
  TApp ndef $ map (assert_total $ findSelfVar x) defs
findSelfVar x (FRef y) = if x == y then FRef "__self__" else FRef y

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
||| @name : The name of the Type
||| @replacement : the replacement function for self references
||| @defs : the type definitions of each data constructor
findRecusion : (name : String) -> (replacement : String -> TDef i -> TDef i) -> (defs : Vect n (TDef i))
            -> Vect n (TDef (S i))
findRecusion name replacement defs {i} = map findRec defs
  where
    findRec : TDef i -> TDef (S i)
    findRec def =
      let self = replacement name def   -- First replace all self application by __self__
          shifted = shiftVars self -- Then shift all vars
       in replaceRef name shifted  -- Finally replace __self__ by FZ

checkDefs : Vect n a -> CompilerM (k ** Vect (2 + k) a)
checkDefs [x, y] = pure (Z ** [x, y])
checkDefs (x :: xs) = do (n ** ns) <- checkDefs xs
                         pure (S n ** x :: ns)
checkDefs _ = raise "enum doesn't have at least two constructors"

||| Compile an enum syntax down to a TMu
||| @name the name given to the type
||| @constructors the list of constructors for each value
compileEnum : (name : String) -> (args : List String)
           -> (constructors : Vect m (String, TDef l))
           -> CompilerM (TNamed l)
compileEnum name args constructors = do
  (k ** checkedDefs) <- checkDefs constructors
  let replacementPolicy = if isNil args then findSelfVar else findSelfApp
  let recursed = findRecusion name replacementPolicy (map snd checkedDefs)
  let pairs = zip (map fst checkedDefs) recursed
  pure (TName name (TMu pairs))

compileDef : AST.TopLevelDef -> CompilerM (n ** TNamed n)
compileDef (MkTopLevelDef (MkDefName defn args) (Simple x)) = do
  c <- compileAppli args x
  let flattened = flattenExpressionTree c
  pure (List.length args ** TName defn flattened)
compileDef (MkTopLevelDef (MkDefName n args) (Enum xs)) = do
  exprDef <- traverseEffect (\(n, d) => MkPair n <$> (compileAppli args d)) (fromList xs)
                       -- inner map is to map across pairs
  let flattened = map (map flattenExpressionTree) exprDef
  pure $ (length args ** !(compileEnum n args flattened))
compileDef (MkTopLevelDef def (Record xs)) = raise "records are not supported at this time"


export
compileEither : AST.TopLevelDef -> Either String (n ** TNamed n)
compileEither ast = run (compileDef ast)

listDef : AST.TopLevelDef
listDef = MkTopLevelDef (MkDefName "List" ["a"])
  (Enum [ ("Nil", AEmb $ EEmb $ TEmb $ FEmb $ PLit 1)
        , ("Cons", AEmb $ EEmb $ TMul (TEmb $ FEmb $ PRef "a")

                   (FEmb $ PEmb $ AST.App "List" (MkNEList (EEmb $ TEmb $ FEmb $ PRef "a") [])))])
