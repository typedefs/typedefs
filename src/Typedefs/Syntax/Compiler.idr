module Typedefs.Syntax.Compiler

import Data.Vect

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

||| Return the index of the given element in the context, extend accordingly
||| More precisely: Given a list of elements, a context as a vector and an
||| element, return the index of the element inside the context. If it cannot
||| be found this function will raise an error. If it cannot be found in context
||| but can be found in the list then extend the context with the missing element.
mkVariableCtx : Show a => Eq a => (ls : List a) -> (e : a) -> (state : Vect m a)
             -> CompilerM (n ** (m `LTE` (S n), Fin (S n), Vect (S n) a))
mkVariableCtx ls e state {m} with (Vect.findIndex (== e) state)
  mkVariableCtx ls e state {m}     | Nothing with (find (== e) ls)
    mkVariableCtx ls e state {m}   | Nothing | Nothing  = raise $ "not found: " ++ show e
    mkVariableCtx ls e state {m}   | Nothing | (Just x) = pure (m ** ( trivialLTE m
                                                                     , last
                                                                     , rewrite succPlus m in state ++ [x]))
  mkVariableCtx ls e state {m=S m} | Just i  = pure (m ** (LTESucc lteRefl, i, state))

mutual
  ||| Fold over a dependent type. The result are both a TDef and its context.
  ||| The TDef is weakened accordingly when the context grows which is why we
  ||| need the `LTE` proof.
  foldIndexify : List String -> {m, k : Nat} -> (acc : (Vect k (TDef m)))
              -> (ctx : Vect m String) -> Vect l (TDef Z)
              -> CompilerM (n ** (m `LTE` n, Vect l (TDef n), Vect n String))
  foldIndexify args acc ctx [] {m} = pure (m ** (lteRefl, [], ctx))
  foldIndexify args acc ctx (def :: defs) = do
    (a ** (lteprf, newdef, newctx)) <- indexify args ctx def
    let weak = map (\tdef => weakenTDef tdef a lteprf) acc
    (b ** (lteprf', restDefs, newctx')) <- foldIndexify args (newdef :: weak) newctx defs
    pure (b ** (lteTransitive lteprf lteprf', weakenTDef newdef b lteprf' :: restDefs, newctx'))

  ||| Give index to all free references
  ||| More specifically it will:
  |||  - Replace all FRef by a TVar pointing to its index in the context
  |||  - update the context with new variables when they are not in context
  |||  - throw when a variable cannot be found
  indexify : List String -> (ctx : Vect m String) -> TDef Z
          -> CompilerM (n ** (m `LTE` n, TDef n, Vect n String))
  indexify args ctx T0 {m} = pureM (m ** (lteRefl, T0, ctx))
  indexify args ctx T1 {m} = pureM (m ** (lteRefl, T1, ctx))
  indexify args ctx (TSum xs) {m} = do
    (a ** (prf, args, newctx)) <- foldIndexify args [] ctx xs
    pure (a ** (prf, TSum args, newctx))
  indexify args ctx (TProd xs) {m} = do
    (a ** (prf, args, newctx)) <- foldIndexify args [] ctx xs
    pure (a ** (prf, TProd args, newctx))
  indexify args ctx (FRef ref) = do (l ** (prf, index, newCtx)) <- mkVariableCtx args ref ctx
                                    pure (S l ** (prf, TVar index, newCtx))
  indexify args ctx _ = raise "shouldn't happen, lol typechecking amirite"


maximize : Vect (S k) (n ** TDef n) -> (m ** Vect (S k) (TDef m))
maximize vect = let (n ** max) = toVMax vect in
                    (n ** map (\(_ ** (lte, td)) => weakenTDef td n lte) (fromVMax max))

containsRef' : String -> TDef i -> Bool
containsRef' x T0 = False
containsRef' x T1 = False
containsRef' x (TSum ys) = any (assert_total $ containsRef' x) ys
containsRef' x (TProd ys) = any (assert_total $ containsRef' x) ys
containsRef' x (TVar i) = False
containsRef' x (TMu ys) = any (assert_total $ containsRef' x) (map snd ys)
containsRef' x (TApp y ys) = False
containsRef' x (FRef y) = x == y

replaceRef : String -> TDef i -> TDef (S i)
replaceRef x T0 = T0
replaceRef x T1 = T1
replaceRef x (TSum ys) = TSum $ map (assert_total $ replaceRef x) ys
replaceRef x (TProd ys) = TProd $ map (assert_total $ replaceRef x) ys
replaceRef x (TVar n) = TVar (FS n)
replaceRef x (TMu ys) = TMu $ map (map $ assert_total (replaceRef x)) ys
replaceRef x (TApp (TName n d) ys) = ?whut
replaceRef x (FRef y) = if x == y then TVar FZ else FRef y


weakenIfRef : String -> (t : TDef i) -> Nat
weakenIfRef name tdef {i} = case containsRef' name tdef of
                                 True => (S i)
                                 False => i

replaceRec : (n : String) -> (t : TDef i) -> TDef (weakenIfRef n t)
replaceRec name t with (containsRef' name t)
  | True = replaceRef name t
  | False = t


||| Given a name and a vector of TDef, replace references pointing to the name with `Var 0`
||| This also either weakens or increments all references
findRecusion : String -> Vect n (TDef i) -> Vect n (TDef (S i))
findRecusion name xs = if any (containsRef' name) xs
                          then map (replaceRef name) xs
                          else weakenAll xs
  where
    weakenAll : Vect n (TDef i) -> Vect n (TDef (S i))
    weakenAll vect {i} = map (\def => weakenTDef def (S i) (trivialLTE i)) vect

||| Given the name of an enum and the name of its argument construct a correctly indexed TDef
indexEnum : (name : String) -> (args : List String)
         -> TDef Z -> Eff (n ** TDef n) [EXCEPTION String]
indexEnum name args tdef = do (n ** (_, newTDef, ctx)) <- indexify args [name] tdef
                              pure (n ** newTDef)

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
  let recursed = findRecusion name (map snd checkedDefs)
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
                                      (FEmb $ PEmb $ Ref "List"))])
