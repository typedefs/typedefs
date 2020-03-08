||| Data to represent Haskell source code
module Typedefs.Backend.Haskell.Data

import Typedefs.Names
import Typedefs.Backend.Data
import Data.Vect

||| The syntactic structure of (a subset of) Haskell terms.
public export
data HsTerm : Type where
  ||| The unit term `()`.
  HsUnitTT : HsTerm
  ||| The tuple constructor, containing two or more further terms.
  HsTupC : Vect n HsTerm -> HsTerm

  ||| A term variable, with a name (no need for deBruijn indices when terms are first-order!).
  HsTermVar : Name -> HsTerm

  ||| The wildcard pattern `_`.
  HsWildcard : HsTerm

  ||| A data type constructor, containing a name and a list of further terms.
  HsInn : Name -> List HsTerm -> HsTerm

  ||| A case expression, containing a term being examined, and a list
  ||| of (lhs, rhs) pairs. Invariants: lhs is a pattern (ie all
  ||| variables occur linearly), and FreeVars(rhs) \subseteq
  ||| FreeVars(lhs).
  HsCase : HsTerm -> List (HsTerm, HsTerm) -> HsTerm

  ||| A function application.
  HsApp : HsTerm -> List HsTerm -> HsTerm

  ||| (The name of) a function.
  HsFun : Name -> HsTerm

  ||| Do-notation: A list of statements of the form
  |||   x <- e    [ represented by (Just x, e)
  ||| or simply
  |||   e         [ represented by (Nothing, e)].
  HsDo : List (Maybe HsTerm, HsTerm) -> HsTerm

  -- special constants (for convenience)

  ||| A Word8 converted from an Int literal (`fromIntegral i`).
  HsWord8 : Int -> HsTerm

  ||| An Int literal.
  HsInt : Integer -> HsTerm

  ||| `mconcat :: [Builder] -> Builder` from Data.ByteString.Builder.
  HsConcat : List HsTerm -> HsTerm

||| The syntactic structure of Haskell types.
public export
data HsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  HsVoid  :                                HsType

  ||| The `()` (i.e. unit/singleton) type.
  HsUnit  :                                HsType

  ||| The tuple type, containing two or more further types.
  HsTuple :         Vect (2 + n) HsType -> HsType

  ||| The sum type, containing two further types.
  HsSum   :         HsType -> HsType    -> HsType

  ||| A type variable.
  HsVar   :         Name                -> HsType

  ||| A named type with zero or more other types as parameters.
  HsParam : Name -> Vect n HsType       -> HsType

  ||| A function type (only used for top-level type of termdef
  ||| decoders and encoders)
  HsArrow :         HsType -> HsType    -> HsType

printType : HsType -> String
printType  HsVoid        = "Void"
printType  HsUnit        = "()"
printType (HsTuple xs)   = "(" ++ concat (intersperse ", " (map (assert_total printType) xs)) ++ ")"
printType (HsSum x y)    = "(Either " ++ printType x ++ printType y ++ ")"
printType (HsVar x)      = x
printType (HsParam x xs) = x ++ concat (intersperse " " (map (assert_total printType) xs))
printType (HsArrow x y)  = printType x ++ " -> " ++ printType y

export
Show HsType where
  show = printType

export
Eq HsType where
  HsVoid == HsVoid = True
  HsUnit == HsUnit = True
  (HsTuple l {n = nl} ) == (HsTuple r {n = nr}) with (decEq nl nr)
    (HsTuple l {n = nl} ) == (HsTuple r {n = nl}) | Yes Refl = assert_total $ l == r
    (HsTuple l {n = nl} ) == (HsTuple r {n = nr}) | No _ = False
  (HsSum xl yl)  == (HsSum xr yr)  = xl == xr && yl == yr
  (HsVar l) == (HsVar r) = l == r
  (HsParam xl yl {n = nl}) == (HsParam xr yr {n = nr}) with (decEq nl nr)
    (HsParam xl yl {n = nl}) == (HsParam xr yr {n = nl}) | Yes Refl =
      assert_total $ xl == xr && yl == yr
    (HsParam xl yl {n = nl}) == (HsParam xr yr {n = nr}) | No _ = False
  (HsArrow xl yl) == (HsArrow xr yr) = xl == xr && yl == yr
  _ == _ = False

export
hsNamed : Name -> HsType
hsNamed n = HsParam n []

||| The syntactic structure of Haskell type declarations.
public export
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                               -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect n (Name, HsType)                -> Haskell

  ||| A function definition is a declared name, a type, and a list of
  ||| clauses of the form ((arg1, ..., argk), rhs).
  FunDef  : Name -> HsType -> List (List HsTerm, HsTerm) -> Haskell
