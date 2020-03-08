module Typedefs.Backend.Haskell.Typegen

import Text.PrettyPrint.WL
import Data.Vect

import Typedefs.Typedefs
import Typedefs.Names
import Typedefs.Backend.Utils
import Typedefs.Backend.Haskell.Data

%default total

||| Generate a Haskell type from a `TDef`.
export
makeType : Vect n HsType -> TDefR n -> HsType
makeType _    T0          = HsVoid
makeType _    T1          = HsUnit
makeType e    (TSum xs)   = foldr1' HsSum $ map (assert_total $ makeType e) xs
makeType e    (TProd xs)  = HsTuple $ map (assert_total $ makeType e) xs
makeType e    (TVar v)    = Vect.index v e
makeType e td@(TMu cases) = HsParam (nameMu cases) $ getUsedVars e td
makeType e    (TApp f xs) = HsParam (name f) $ map (assert_total $ makeType e) xs
makeType e    (RRef i)    = index i e

||| Generate a Haskell type from a `TNamed`.
export
makeType' : Vect n HsType -> TNamedR n -> HsType
makeType' e (TName ""   body) = makeType e body --escape hatch; used e.g. for all non-TApp dependencies of a TApp
makeType' e (TName name body) = HsParam name $ getUsedVars e body

||| The same as `tupled : List Doc -> Doc`, except that tuples with
||| more than 62 components get turned into nested tuples, to adhere
||| to GHC's restriction on tuple size.
||| (See https://hackage.haskell.org/package/ghc-prim-0.5.1.0/docs/src/GHC.Tuple.html )
export
hsTupled : List Doc -> Doc
hsTupled xs = if length xs < 63
              then tupled xs
              else let (xs0, xs1) = splitAt 61 xs in
                   tupled (xs0 ++ [hsTupled $ assert_smaller xs xs1])

export
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  ||| Render a type signature as Haskell source code.
  export
  renderType : HsType -> Doc
  renderType HsVoid                = text "Void"
  renderType HsUnit                = text "()"
  renderType (HsTuple xs)          = hsTupled . toList . map (assert_total renderType) $ xs
  renderType (HsSum a b)           = renderApp "Either" [guardParen a, guardParen b]
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)
  renderType (HsArrow a b)         = renderArrow (renderParamNoParen a) b
    where
      -- Parenthesize, except for Param (since e.g. type application binds stronger than ->)
      renderParamNoParen : HsType -> Doc
      renderParamNoParen a@(HsParam _ _) = renderType a
      renderParamNoParen a               = guardParen a

      renderArrow : Doc -> HsType -> Doc
      renderArrow a (HsArrow b' c') = a |++| text "->" |++| (renderArrow (renderParamNoParen b') c')
      renderArrow a b               = a |++| text "->" |++| (renderParamNoParen b)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  export
  guardParen : HsType -> Doc
  guardParen t@(HsParam _ []) = assert_total $ renderType t
  guardParen t@(HsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t@(HsSum _ _ )   = parens (assert_total $ renderType t)
  guardParen t@(HsArrow _ _)  = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t
