
module Backend.Swift

import Names
import Typedefs

import Text.PrettyPrint.WL
import Backend
import Backend.Utils
 
import Data.Vect

%default total
%access export

data SwType : Type where

  ||| The empty type is represented with `Never 
  SwVoid  :                           SwType

  ||| The unit type is represented with `()`
  SwUnit  :                           SwType

  ||| The tuple type, containing two or more further types.
  SwTuple : Vect (2 + n) SwType    -> SwType

  ||| A type variable.
  SwVar   : Name                   -> SwType

  ||| A named type with zero or more other types as parameters.
  SwParam : Name -> Vect n SwType  -> SwType


data Swift : Type where

  ||| A type synonym
  Typealias : Decl -> SwType -> Swift
  Record    : Decl -> Vect n (Name, SwType) -> Swift
  Enum      : Decl -> Vect n (Name, SwType) -> Swift

renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) 
                        |+| text "<" 
                          |+| hcat (intersperse (text ", ") (empty :: toList params))
                        |+| text ">"

mutual
  ||| Render a type signature as Haskell source code.
  renderType : SwType -> Doc
  renderType SwVoid                = text "Never"
  renderType SwUnit                = text "()"
  renderType (SwTuple xs)          = tupled . toList . map (assert_total renderType) $ xs
  renderType (SwVar v)             = text (uppercase v)
  renderType (SwParam name params) = renderApp name (map guardParen params)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : SwType -> Doc
  guardParen t@(SwParam _ []) = assert_total $ renderType t
  guardParen t@(SwParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

renderFields : Vect n (Name, SwType) -> List Doc
renderFields fields = map (\(n, tpe) => text "let" |++| text n |+| text ":" |++| renderType tpe) $ toList fields

renderCases : Vect n (Name, SwType) -> List Doc
renderCases cases = map (\(n, tpe) => text "case" |++| text n |+| parens (punctuate ", " (renderCaseTuple tpe))) $ toList cases
  where renderCaseTuple : SwType -> List Doc

||| Render a type definition as Swift source code.
renderDef : Swift -> Doc
renderDef (Typealias lhs rhs) = text "typealias" |++| renderDecl lhs 
                                 |++| equals |++| renderType rhs
renderDef (Record decl fields) = text "struct" |++| renderDecl decl |++| text "{"
                                    |$$| (vsep $ renderFields fields)
                                    |$$| text "}"
renderDef (Enum   decl cases) = text "enum" |++| renderDecl decl |++| text "{" 
                                            |$$| vsep (renderCases cases)
                                            |$$| text "}"

--   where
--   renderConstructor : (Name, SwType) -> Doc
--   renderConstructor (name, SwUnit)     = renderApp name []
--   renderConstructor (name, SwTuple ts) = renderApp name (map guardParen ts)
--   renderConstructor (name, params)     = renderApp name [guardParen params]

private
swiftParam : Decl -> SwType
swiftParam (MkDecl n ps) = SwParam n (map SwVar ps)

private
freshEnv : Env n
freshEnv = freshEnv "A"

||| Generate a Swift type from a `TNamed`.
makeType' : Env n -> TNamed n -> SwType
makeType' e (TName name body) = SwParam name . map (either SwVar swiftParam) $ getUsedVars e body

ASTGen Swift SwType n where
  msgType = makeType' freshEnv
  generateTyDefs x = ?ASTGen_rhs_2

CodegenIndep Swift SwType where
  typeSource = renderType
  defSource = renderDef
