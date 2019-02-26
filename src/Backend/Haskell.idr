module Backend.Haskell

import Types
import Typedefs

import Backend
import Backend.Utils

import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect

%default total
%access export

||| The syntactic structure of Haskell types.
data HsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  HsVoid  :                                HsType

  ||| The `()` (i.e. unit/singleton) type.
  HsUnit  :                                HsType

  ||| The tuple type, containing two or more further types.
  HsTuple :         Vect (2 + n) HsType -> HsType

  ||| A type variable.
  HsVar   :         Name                -> HsType

  ||| A named type with zero or more other types as parameters.
  HsParam : Name -> Vect n HsType       -> HsType

||| The syntactic structure of Haskell type declarations.
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect n (Name, HsType) -> Haskell

-- Haskell type variables start with lowercase letters.
private
freshEnv : Env n
freshEnv = freshEnv "x"

||| Render a name applied to a list of arguments exactly as written.
||| Arguments need to be previously parenthesized, if applicable.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  ||| Render a type signature as Haskell source code.
  renderType : HsType -> Doc
  renderType HsVoid                = text "Void"
  renderType HsUnit                = text "()"
  renderType (HsTuple xs)          = tupled . toList . map (assert_total renderType) $ xs
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : HsType -> Doc
  guardParen t@(HsParam _ []) = assert_total $ renderType t
  guardParen t@(HsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

||| Render a type definition as Haskell source code.
renderDef : Haskell -> Doc
renderDef (Synonym decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
renderDef (ADT     decl cases) = text "data" |++| renderDecl decl
                                 |++| equals |++| hsep (punctuate (text " |")
                                                       (toList $ map renderConstructor cases))
  where
  renderConstructor : (Name, HsType) -> Doc
  renderConstructor (name, HsUnit)     = renderApp name []
  renderConstructor (name, HsTuple ts) = renderApp name (map guardParen ts)
  renderConstructor (name, params)     = renderApp name [guardParen params]

private
hsParam : Decl -> HsType
hsParam (MkDecl n ps) = HsParam n (map HsVar ps)

||| Generate a Haskell type from a `TDef`.
makeType : Env n -> TDef n -> HsType
makeType _    T0          = HsVoid
makeType _    T1          = HsUnit
makeType e    (TSum xs)   = foldr1' (\t1,t2 => HsParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType e    (TProd xs)  = HsTuple $ map (assert_total $ makeType e) xs
makeType e    (TVar v)    = either HsVar hsParam $ Vect.index v e
makeType e td@(TMu cases) = HsParam (nameMu cases) . map (either HsVar hsParam) $ getUsedVars e td
makeType e    (TApp f xs) = HsParam (name f) (map (assert_total $ makeType e) xs)

||| Generate a Haskell type from a `TNamed`.
makeType' : Env n -> TNamed n -> HsType
makeType' e (TName name body) = HsParam name . map (either HsVar hsParam) $ getUsedVars e body

mutual
  ||| Generate all the Haskell type definitions that a `TDef` depends on.
  makeDefs : TDef n -> State (List Name) (List Haskell)
  makeDefs    T0          = pure []
  makeDefs    T1          = pure []
  makeDefs    (TProd xs)  = map concat $ traverse (assert_total makeDefs) xs
  makeDefs    (TSum xs)   = map concat $ traverse (assert_total makeDefs) xs
  makeDefs    (TVar v)    = pure []
  makeDefs td@(TMu cases) = makeDefs' $ TName (nameMu cases) td -- We name anonymous mus using their constructors.
  makeDefs    (TApp f xs) = do
      res <- assert_total $ makeDefs' f
      res' <- concat <$> traverse (assert_total makeDefs) xs
      pure (res ++ res')

  ||| Generate Haskell type definitions for a `TNamed` and all of its dependencies.
  makeDefs' : TNamed n -> State (List Name) (List Haskell)
  makeDefs' (TName name body) = ifNotPresent name $ 
      let decl = MkDecl name (getFreeVars $ getUsedVars freshEnv body) in -- All vars will actually be free, but we want Strings instead of Eithers.
      case body of
        TMu cases => do -- Named `TMu`s are treated as ADTs.
          let newEnv = Right decl :: freshEnv
          let args = map (map (makeType newEnv)) cases
          res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs bdy) (toList cases)
          pure $ ADT decl args :: res
        _ => do -- All other named types are treated as synonyms.
          res <- assert_total $ makeDefs body
          pure $ Synonym decl (makeType freshEnv body) :: res

ASTGen Haskell HsType n where
  msgType          = makeType' freshEnv
  generateTyDefs tn      = reverse $ evalState (makeDefs' tn) []

CodegenIndep Haskell HsType where
  typeSource = renderType
  defSource  = renderDef
