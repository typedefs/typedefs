module Backend.ReasonML

import Types
import Typedefs

import Backend
import Backend.Utils

import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect

%default total
%access public export

||| The syntactic structure of ReasonML types.
data RMLType : Type where
  ||| The `unit` (i.e. singleton) type.
  RMLUnit  :                                  RMLType

  ||| The tuple type, containing two or more further types.
  RMLTuple  :         Vect (2 + k) RMLType -> RMLType

  ||| A type variable.
  RMLVar   :         Name                  -> RMLType

  ||| A named type with zero or more other types as parameters.
  RMLParam : Name -> Vect k RMLType        -> RMLType

||| The syntactic structure of ReasonML type declarations.
data ReasonML : Type where
  ||| A type alias is a declared name (possibly with parameters) and a type.
  Alias   : Decl -> RMLType                -> ReasonML

  ||| A variant is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a ReasonML type.
  Variant : Decl -> Vect k (Name, RMLType) -> ReasonML

||| Render a name as a type variable.
renderVar : Name -> Doc
renderVar v = squote |+| text (lowercase v)

||| Given a name and a vector of arguments, render an application of the name to the arguments.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text name |+| case params of
                                        [] => empty
                                        _  => tupled (toList params)

||| Render source code for a ReasonML type signature.
renderType : RMLType -> Doc
renderType RMLUnit                = text "unit"
renderType (RMLTuple xs)          = tupled . toList $ map (assert_total renderType) xs
renderType (RMLVar v)             = renderVar v
renderType (RMLParam name params) = renderApp (lowercase name) . map (assert_total renderType) $ params

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (lowercase $ name decl) (map renderVar $ params decl)

||| Generate source code for a ReasonML type definition.
renderDef : ReasonML -> Doc
renderDef (Alias   decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
                                 |+| semi
renderDef (Variant decl cases) = text "type" |++| renderDecl decl
                                 |+| case cases of
                                       [] => empty
                                       _  => space |+| equals |++| hsep (punctuate (text " |") (toList $ map renderConstructor cases))
                                 |+| semi
  where
  renderConstructor : (Name, RMLType) -> Doc
  renderConstructor (name, RMLUnit)     = renderApp (uppercase name) []
  renderConstructor (name, RMLTuple ts) = renderApp (uppercase name) (map renderType ts)
  renderConstructor (name, t)           = renderApp (uppercase name) [renderType t]

anonMu : Vect n (Name, a) -> Name
anonMu = concatMap (uppercase . fst)

rmlParam : Decl -> RMLType
rmlParam (MkDecl n ps) = RMLParam n (map RMLVar ps)

||| Generate a ReasonML type from a `TDef`.
makeType : Env n -> TDef n -> RMLType
makeType _ T0             = RMLParam "void" []
makeType _ T1             = RMLUnit
makeType e (TSum xs)      = foldr1' (\t1,t2 => RMLParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType e (TProd xs)     = RMLTuple . map (assert_total $ makeType e) $ xs
makeType e (TVar v)       = either RMLVar rmlParam $ Vect.index v e
makeType e td@(TMu cases) = RMLParam (anonMu cases) . map (either RMLVar rmlParam) $ getUsedVars e td
makeType e (TApp f xs)    = RMLParam (name f) (map (assert_total $ makeType e) xs)

mutual
   ||| Generate ReasonML type definitions from a `TDef`, includig all of its dependencies.
   makeDefs : TDef n -> State (List Name) (List ReasonML)
   makeDefs T0            = assert_total $ makeDefs' voidDef
     where
     voidDef : TNamed 0
     voidDef = TName "void" $ TMu []
   makeDefs T1            = pure []
   makeDefs (TProd xs)    = map concat $ traverse (assert_total makeDefs) xs
   makeDefs (TSum xs)     =
     do res <- map concat $ traverse (assert_total makeDefs) xs
        map (++ res) (assert_total $ makeDefs' eitherDef)
     where
     eitherDef : TNamed 2
     eitherDef = TName "either" $ TMu [("Left", TVar 1), ("Right", TVar 2)]
   makeDefs (TVar v)      = pure []
   makeDefs (TApp f xs) = do
     res <- assert_total $ makeDefs' f
     res' <- concat <$> traverse (assert_total makeDefs) xs
     pure (res ++ res')
   makeDefs td@(TMu cases) = makeDefs' $ TName (anonMu cases) td -- We name anonymous mus using their constructors.
   {-
   makeDefs e td@(TName name body) =
     do st <- get
        if List.elem name st then pure []
          else
           do res <- assert_total $ makeDefs e body
              put (name :: st)
              pure $ Alias (MkDecl name (getFreeVars $ getUsedVars e td)) (makeType e body) :: res
   -}

   makeDefs' : TNamed n -> State (List Name) (List ReasonML)
   makeDefs' (TName name body) = do
      st <- get
      if List.elem name st then pure []
      else do
        let decl = MkDecl name (getFreeVars $ getUsedVars (freshEnvLC _) body)
        put (name :: st)
        case body of
          TMu cases => do -- Named `TMu`s are treated as ADTs.
            let newEnv = Right decl :: freshEnvLC _
            let args = map (map (makeType newEnv)) cases
            res <- map concat $ traverse {b=List ReasonML} (\(_, bdy) => assert_total $ makeDefs bdy) (toList cases)
            pure $ Variant decl args :: res
          _         => do -- All other named types are treated as synonyms.
            res <- assert_total $ makeDefs body
            pure $ Alias decl (makeType (freshEnvLC n) body) :: res


Backend ReasonML where
  generateTyDefs e tn = reverse $ evalState (makeDefs' tn) []
  generateCode        = renderDef
  freshEnv            = freshEnvLC

NewBackend ReasonML RMLType where
  msgType = makeType (freshEnv {lang=ReasonML} 0)
  typedefs tn = reverse $ evalState (makeDefs' tn) []
  source type defs = vsep2 $ map renderDef $ defs ++ [Alias (MkDecl "TypedefSchema" []) type]

||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
generateType : TDef n -> Doc
generateType {n} = renderType . makeType (freshEnv {lang=ReasonML} n)
