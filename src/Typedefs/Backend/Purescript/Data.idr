||| Data to represent Purescript source code
module Typedefs.Backend.Purescript.Data

import Typedefs.Names
import Typedefs.Backend.Data
import Data.Vect

||| The syntactic structure of (a subset of) Purescript terms.
public export
data PsTerm : Type where
  ||| The unit term `()`.
  PsUnitTT : PsTerm
  ||| The tuple constructor, containing two or more further terms.
  PsTupC : Vect n PsTerm -> PsTerm

  ||| A term variable, with a name (no need for deBruijn indices when terms are first-order!).
  PsTermVar : Name -> PsTerm

  ||| The wildcard pattern `_`.
  PsWildcard : PsTerm

  ||| A data type constructor, containing a name and a list of further terms.
  PsInn : Name -> List PsTerm -> PsTerm

  ||| A case expression, containing a term being examined, and a list
  ||| of (lPs, rPs) pairs. Invariants: lPs is a pattern (ie all
  ||| variables occur linearly), and FreeVars(rPs) \subseteq
  ||| FreeVars(lPs).
  PsCase : PsTerm -> List (PsTerm, PsTerm) -> PsTerm

  ||| A function application.
  PsApp : PsTerm -> List PsTerm -> PsTerm

  ||| (The name of) a function.
  PsFun : Name -> PsTerm

  ||| Do-notation: A list of statements of the form
  |||   x <- e    [ represented by (Just x, e)
  ||| or simply
  |||   e         [ represented by (Nothing, e)].
  PsDo : List (Maybe PsTerm, PsTerm) -> PsTerm

  -- special constants (for convenience)

  ||| A Word8 converted from an Int literal (`fromIntegral i`).
  PsWord8 : Int -> PsTerm

  ||| An Int literal.
  PsInt : Integer -> PsTerm

  ||| `mconcat :: [Builder] -> Builder` from Data.ByteString.Builder.
  PsConcat : List PsTerm -> PsTerm

||| The syntactic structure of Purescript types.
public export
data PsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  PsVoid  :                                PsType

  ||| The `()` (i.e. unit/singleton) type.
  PsUnit  :                                PsType

  ||| The tuple type, containing two or more further types.
  PsTuple :         Vect (2 + n) PsType -> PsType

  ||| The sum type, containing two further types.
  PsSum   :         PsType -> PsType    -> PsType

  ||| A type variable.
  PsVar   :         Name                -> PsType

  ||| A named type with zero or more other types as parameters.
  PsParam : Name -> Vect n PsType       -> PsType

  ||| A function type (only used for top-level type of termdef
  ||| decoders and encoders)
  PsArrow :         PsType -> PsType    -> PsType

printType : PsType -> String
printType  PsVoid        = "Void"
printType  PsUnit        = "()"
printType (PsTuple xs)   = "(" ++ concat (intersperse " /\\ " (map (assert_total printType) xs)) ++ ")"
printType (PsSum x y)    = "(Either " ++ printType x ++ printType y ++ ")"
printType (PsVar x)      = x
printType (PsParam x xs) = x ++ concat (intersperse " " (map (assert_total printType) xs))
printType (PsArrow x y)  = printType x ++ " -> " ++ printType y

export
Show PsType where
  show = printType

export
Eq PsType where
  PsVoid == PsVoid = True
  PsUnit == PsUnit = True
  (PsTuple l {n = nl} ) == (PsTuple r {n = nr}) with (decEq nl nr)
    (PsTuple l {n = nl} ) == (PsTuple r {n = nl}) | Yes Refl = assert_total $ l == r
    (PsTuple l {n = nl} ) == (PsTuple r {n = nr}) | No _ = False
  (PsSum xl yl)  == (PsSum xr yr)  = xl == xr && yl == yr
  (PsVar l) == (PsVar r) = l == r
  (PsParam xl yl {n = nl}) == (PsParam xr yr {n = nr}) with (decEq nl nr)
    (PsParam xl yl {n = nl}) == (PsParam xr yr {n = nl}) | Yes Refl =
      assert_total $ xl == xr && yl == yr
    (PsParam xl yl {n = nl}) == (PsParam xr yr {n = nr}) | No _ = False
  (PsArrow xl yl) == (PsArrow xr yr) = xl == xr && yl == yr
  _ == _ = False

export
psNamed : Name -> PsType
psNamed n = PsParam n []

||| The syntactic structure of Purescript type declarations.
public export
data Purescript : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> PsType                               -> Purescript

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Purescript type.
  ADT     : Decl -> Vect n (Name, PsType)                -> Purescript

  ||| A function definition is a declared name, a type, and a list of
  ||| clauses of the form ((arg1, ..., argk), rPs).
  FunDef  : Name -> PsType -> List (List PsTerm, PsTerm) -> Purescript
