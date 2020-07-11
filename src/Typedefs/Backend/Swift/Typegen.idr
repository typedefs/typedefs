module Typedefs.Backend.Swift.Typegen

import Typedefs.Backend.Swift.Data
import Typedefs.Backend.Data
import Typedefs.Backend
import Data.Vect
import Typedefs.Names

import Typedefs.Test

import Text.PrettyPrint.WL

%default total

encloseEmpty : Doc -> Doc -> Doc -> List Doc -> Doc
encloseEmpty l r sep [] = empty
encloseEmpty l r sep ls = encloseSep l r sep ls

chevrons : List Doc -> Doc
chevrons = encloseEmpty (text "<") (text ">") comma

tupled' : List Doc -> Doc
tupled' = encloseEmpty lparen rparen comma

underscore : Doc
underscore = text "_"

arrow : Doc
arrow = text "->"

genSwiftTypes : SwType -> Doc
genSwiftTypes SwVoid = text "void()"
genSwiftTypes SwUnit = text "()"
genSwiftTypes (SwTuple ts) = tupled (map (assert_total genSwiftTypes) ts)
genSwiftTypes (SwEither l r) = text "Result" |+| chevrons [genSwiftTypes l, genSwiftTypes r]
genSwiftTypes (SwFun args ret) = tupled (map (assert_total genSwiftTypes) args) |++| arrow |++| genSwiftTypes ret
genSwiftTypes (SwTApp n args) = text n |+| chevrons (map (assert_total genSwiftTypes) args)

genCase : (Name, List SwType) -> Doc
genCase (constr, types) = text "case" |++| dot |+| text constr |+| tupled' (map genSwiftTypes types)

genField : (Name, SwType) -> Doc
genField (field, type) = text "let" |++| text field |++| colon |++| genSwiftTypes type

genFunArg : (Name, SwType) -> Doc
genFunArg (argName, type) = underscore |++| text argName |++| colon |++| genSwiftTypes type

renderIndirect : IsIndirect -> Doc -> Doc
renderIndirect Indirect rest = text "indirect" |++| rest
renderIndirect _ rest = rest

genSwiftDecl : SwTypeDecl -> Doc
genSwiftDecl (TypeAlias (MkDecl name params) rhs) =
  text "typealias" |++| text name |+| chevrons (toList $ map text params) |++| equals |++| genSwiftTypes rhs
genSwiftDecl (Enum indirect (MkDecl name params) cases) =
  renderIndirect indirect
    (text "enum" |++| text name |+| chevrons (toList $ map text params)
    |++| (braces . indent 4 . vcat . map genCase) cases)
genSwiftDecl (Struct (MkDecl name params) fields) =
  text "struct" |+| text name |+| chevrons (toList $ map text params)
    |++| (braces . indent 4 . vcat . map genField) fields

CodegenIndep SwTypeDecl SwType where
  typeSource = genSwiftTypes
  defSource = genSwiftDecl
  preamble = text """func void<A>() -> A { fatalError("Reached void") }"""
