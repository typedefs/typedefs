module Typedefs.Backend.JSON

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.Backend
import Typedefs.Backend.Specialisation
import Typedefs.Backend.Utils

import Language.JSON
import Text.PrettyPrint.WL

import Data.NEList
import Data.Vect
import Data.SortedMap

import Effects
import Effect.Exception
import Effect.State

%default total
%access public export

JSONDef : Type
JSONDef = (Name, JSON)

Specialisation JSON where
  specialisedTypes = empty

||| Given `"name"`, create `["name0", "name1", ..., "namen"]`
nary : Name -> Vect n Name
nary name = map ((name ++) . show . finToNat) range

||| Reference a definition.
defRef : Name -> JSON
defRef name = JObject [("$ref", JString $ "#/definitions/" ++ name)]

JSONLookupM : Type -> Type
JSONLookupM t = LookupM JSON t

JSONMakeDefM : Type -> Type
JSONMakeDefM t = MakeDefM JSON t

makeSubSchema' : TNamed' 0 b -> JSON
makeSubSchema' = defRef . name

jsonRefError : String -> CompilerError
jsonRefError n = ReferencesNotSupported ("JSON doesn't support referencesm found ref: " ++ n)


mutual
  makeSubSchema : TDef 0 -> JSONLookupM JSON
  makeSubSchema  T0         = pure $ defRef "emptyType"
  makeSubSchema  T1         = pure $ defRef "singletonType"
  makeSubSchema (TSum ts)   = disjointSubSchema (zip (nary "case") ts)
  makeSubSchema (TProd ts)  = productSubSchema (nary "proj") ts
  makeSubSchema (TMu cs)    = pure $ defRef (nameMu cs)
  makeSubSchema (TApp f []) = pure $ defRef . name $ f
  makeSubSchema (TApp f xs) = pure $ defRef . name $ f `apN` xs
  makeSubSchema (FRef n)    = raise $ jsonRefError n

  ||| Generate a schema that matches exactly one of the supplied schemas, which must be wrapped in its corresponding name.
  disjointSubSchema : Vect k (Name, TDef 0) -> JSONLookupM JSON
  disjointSubSchema cases =
    pure $ JObject [("oneOf", JArray . toList $ !(traverseEffect (assert_total makeCase) cases))]
    where
    isMu : TDef n -> Bool
    isMu (TMu _) = True
    isMu _       = False

    makeCase : (Name, TDef 0) -> JSONLookupM JSON
    makeCase (name, td) = pure $ JObject
      [ ("type", JString "object")
      , ("required", JArray [JString name])
      , ("additionalProperties", JBoolean False)
      , ("properties", JObject [(name, assert_total !(makeSubSchema td))])
      ]

  ||| Generate a schema that requires all of the supplied schemas to match, with each being wrapped in its corresponding name.
  productSubSchema : Vect k Name -> Vect k (TDef 0) -> JSONLookupM JSON
  productSubSchema names tds = pure $ JObject
    [ ("type", JString "object")
    , ("required", JArray . toList $ map JString names)
    , ("additionalProperties", JBoolean False)
    , ("properties", JObject . toList $ Vect.zip names !(traverseEffect (assert_total makeSubSchema) tds))
    ]

mutual
  ||| Generate helper definitions for all types contained in a `TDef 0`.
  makeDefs : TDef 0 -> JSONMakeDefM (List JSONDef)
  makeDefs T0 = ifNotPresent "emptyType" $ pure [("emptyType", emptyType)]
    where
      emptyType : JSON
      emptyType = JObject
                  [ ("type", JString "array")
                  , ("items", JObject [ ("type", JString "boolean") ])
                  , ("minItems", JNumber 3)
                  , ("uniqueItems", JBoolean True)
                  ]
  makeDefs T1 = ifNotPresent "singletonType" $ pure [("singletonType", singletonType)]
      where
      singletonType : JSON
      singletonType = JObject [("enum", JArray [JString "singleton"])]

  makeDefs    (TSum ts)   = concat <$> traverseEffect (assert_total makeDefs) ts
  makeDefs    (TProd ts)  = concat <$> traverseEffect (assert_total makeDefs) ts
  makeDefs td@(TMu cases) = makeDefs' (TName (nameMu cases) td)
  makeDefs    (TApp f []) = makeDefs' f
  makeDefs    (TApp f xs) = makeDefs' (f `apN` xs)
  makeDefs    (FRef n)    = raise $ jsonRefError n

  makeDefs' : TNamed 0 -> JSONMakeDefM (List JSONDef)
  makeDefs' (TName name body) = ifNotPresent name $
    case body of
      TMu cs => do -- Named `TMu`s are treated specially
        let cases = map (map (flattenMus name)) cs
        res <- concat <$> traverseEffect (assert_total $ makeDefs . snd) cases
        pure $ (name, !(disjointSubSchema cases)) :: res
      _ => do -- All other named types are treated as synonyms.
        res <- assert_total $ makeDefs body
        pure $ (name, !(makeSubSchema body)) :: res

||| Takes a schema and a list of helper definitions and puts them together into a top-level schema.
makeSchema : NEList JSON -> List JSONDef -> JSON
makeSchema schema [] = JObject
                  [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                  , ("type", JString "object")
                  , ("required", JArray [JString "value"])
                  , ("additionalProperties", JBoolean False)
                  , ("properties", JObject [ ("value", JObject [("oneOf", JArray $ NEList.toList schema)] ) ])
                  ]
makeSchema schema defs = JObject
                  [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                  , ("type", JString "object")
                  , ("required", JArray [JString "value"])
                  , ("additionalProperties", JBoolean False)
                  , ("definitions", JObject defs)
                  , ("properties", JObject [ ("value", JObject [("oneOf", JArray $ NEList.toList schema)] ) ])
                  ]

ASTGen JSONDef JSON False where
  msgType (Zero tn) = pure $ makeSubSchema' tn
  generateTyDefs tns = runMakeDefM $ concat <$> traverseEffect genDef (toVect tns)
    where
      genDef : ZeroOrUnbounded TNamed False -> JSONMakeDefM (List JSONDef)
      genDef (Zero tn) = makeDefs' tn

  generateTermDefs tns = pure [] -- TODO?

CodegenInterdep JSONDef JSON where
  sourceCode msg defs = literal $ format 2 $ makeSchema msg defs
