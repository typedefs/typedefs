module Typedefs.Backend.Data

import Data.Vect
import Typedefs.Names

||| A parametric type declaration (no definition, only name and parameters).
public export
record Decl where
  constructor MkDecl

  ||| The name of the type.
  name   : Name

  ||| The names of the type's parameters.
  params : Vect n Name -- TODO is number of parameters enough?

||| Errors that the compiler can throw
public export
data CompilerError = RefNotFound String
                   | ReferencesNotSupported String
                   | UnknownError String

export
Semigroup (Either CompilerError a) where
  (Left err) <+> m = m
  (Right v)  <+> _ = Right v

export
Monoid (Either CompilerError a) where
  neutral = Left $ UnknownError "neutral"

export
Show CompilerError where
  show (RefNotFound s) = "Could not find reference " ++ s
  show (ReferencesNotSupported s) = "References are not supported : " ++ s
  show (UnknownError s) = "Unknown error: " ++ s

export
Eq CompilerError where
  (RefNotFound s) == (RefNotFound s') = s == s'
  (ReferencesNotSupported s) == (ReferencesNotSupported s') = s == s'
  _ == _ = False

