module Typedefs.Backend.Swift.Data

import Typedefs.Backend.Data
import Data.Vect
import Typedefs.Names

%access public export

data SwType : Type where
  SwVoid : SwType
  SwUnit : SwType
  SwTuple : List SwType -> SwType
  SwEither : (l, r : SwType) -> SwType
  SwFun : List SwType -> SwType -> SwType
  SwTApp : Name -> List SwType -> SwType

-- Type variable are just applications with no arguments
SwTVar : String -> SwType
SwTVar n = SwTApp n []

Eq SwType where
  (==) SwVoid SwVoid = True
  (==) SwUnit SwUnit = True
  (==) (SwTuple xs) (SwTuple ys) = assert_total $ xs == ys
  (==) (SwEither x v) (SwEither y w) = x == y && v == w
  (==) (SwFun xs x) (SwFun ys y) = (assert_total $ xs == ys) && (x == y)
  (==) (SwTApp n args) (SwTApp m bargs) = n == m && assert_total (args == bargs)
  (==) _ _ = False

data IsIndirect = Indirect | Normal

data SwTypeDecl : Type where
  TypeAlias : Decl -> SwType -> SwTypeDecl
  Enum : IsIndirect-> Decl -> (cases : List (Name, List SwType)) -> SwTypeDecl
  Struct : Decl -> (fields : List (Name, SwType)) -> SwTypeDecl

mutual
  record SwClause where
    constructor MkClause
    name : Name
    patterns : List SwTerm
    body : List SwTerm


  data SwTerm : Type where
    SwVar : Name -> SwTerm
    SwSwitch : SwTerm -> List SwClause -> SwTerm
    SwVarDecl : (mutatble : Bool) ->  Name -> SwTerm -> SwTerm
    SwMethod : (obj : SwTerm) -> (name : Name) -> (args : List SwTerm) -> SwTerm
    SwReturn : SwTerm -> SwTerm
    SwStringLit : String -> SwTerm
    SwIntLit : Int -> SwTerm

data IsStatic = Static | Method

data SwTypeSignature : Type where
  SwFunDecl : IsStatic -> Decl -> (args : List (Name, SwType)) -> (ret : SwType) -> SwTypeSignature

data SwDecl : Type where
  SwDeclType : SwTypeDecl -> SwDecl
  SwFunction : SwTypeSignature -> SwTerm -> SwDecl

  ||| Swift protocol extention declaration
  ||| @typename : Type name and constraints
  ||| @params : Constraints on type parameters
  ||| @body : List of methods to implement
  SwExtention : (typename : Decl) -> (params : List Decl) -> (body : List SwDecl) -> SwDecl

SwFile : Type
SwFile = List SwDecl
