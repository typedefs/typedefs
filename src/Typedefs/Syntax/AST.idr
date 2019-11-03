module Typedefs.Syntax.AST

%access public export

data AnonymousDef = Zero | One
                         | Sum AnonymousDef AnonymousDef
                         | Prod AnonymousDef AnonymousDef
                         | Ref String

record DefName where
  constructor MkDefName
  name : String
  arguments : List String

data Definition
  = Simple AnonymousDef
  | Enum (List (String, AnonymousDef))
  | Record (List (String, AnonymousDef))

record TopLevelDef where
  constructor MkTopLevelDef
  name : DefName
  def : Definition
