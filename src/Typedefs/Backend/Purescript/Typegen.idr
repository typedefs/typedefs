module Typedefs.Backend.Purescript.Typegen

import Text.PrettyPrint.WL
import Data.Vect

import Typedefs.Typedefs
import Typedefs.Names
import Typedefs.Backend.Utils
import Typedefs.Backend.Purescript.Data

%default total

||| Generate a Purescript type from a `TDef`.
export
makeType : Vect n PsType -> TDefR n -> PsType
makeType _    T0          = PsVoid
makeType _    T1          = PsUnit
makeType e    (TSum xs)   = foldr1' PsSum $ map (assert_total $ makeType e) xs
makeType e    (TProd xs)  = PsTuple $ map (assert_total $ makeType e) xs
makeType e    (TVar v)    = Vect.index v e
makeType e td@(TMu cases) = PsParam (nameMu cases) $ getUsedVars e td
makeType e    (TApp f xs) = PsParam (name f) $ map (assert_total $ makeType e) xs
makeType e    (RRef i)    = index i e

||| Generate a Purescript type from a `TNamed`.
export
makeType' : Vect n PsType -> TNamedR n -> PsType
makeType' e (TName ""   body) = makeType e body --escape hatch; used e.g. for all non-TApp dependencies of a TApp
makeType' e (TName name body) = PsParam name $ getUsedVars e body

export
psTupled : List Doc -> Doc
psTupled = encloseSep empty empty (text "/\\")

export
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  ||| Render a type signature as Purescript source code.
  export
  renderType : PsType -> Doc
  renderType  PsVoid               = text "Void"
  renderType  PsUnit               = text "Unit"
  renderType (PsTuple xs)          = psTupled . toList . map (assert_total renderType) $ xs
  renderType (PsSum a b)           = renderApp "Either" [guardParen a, guardParen b]
  renderType (PsVar v)             = text (lowercase v)
  renderType (PsParam name params) = renderApp name (map guardParen params)
  renderType (PsArrow a b)         = renderArrow (renderParamNoParen a) b
    where
      -- Parenthesize, except for Param (since e.g. type application binds stronger than ->)
      renderParamNoParen : PsType -> Doc
      renderParamNoParen a@(PsParam _ _) = renderType a
      renderParamNoParen a               = guardParen a

      renderArrow : Doc -> PsType -> Doc
      renderArrow a (PsArrow b' c') = a |++| text "->" |++| (renderArrow (renderParamNoParen b') c')
      renderArrow a b               = a |++| text "->" |++| (renderParamNoParen b)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  export
  guardParen : PsType -> Doc
  guardParen t@(PsParam _ []) = assert_total $ renderType t
  guardParen t@(PsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t@(PsSum _ _ )   = parens (assert_total $ renderType t)
  guardParen t@(PsArrow _ _)  = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t
