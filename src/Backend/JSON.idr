module Backend.JSON

import Names
import Typedefs

import Backend
import Backend.Utils

import Control.Monad.State
import Language.JSON
import Text.PrettyPrint.WL

import Data.NEList
import Data.Vect

%default total
%access public export

JSONDef : Type
JSONDef = (Name, JSON)

||| Given `"name"`, create `["name0", "name1", ..., "namen"]`
nary : Name -> Vect n Name
nary name = map ((name ++) . show . finToNat) range

||| Reference a definition.
defRef : Name -> JSON
defRef name = JObject [("$ref", JString $ "#/definitions/" ++ name)]

makeSubSchema' : TNamed 0 -> JSON
makeSubSchema' = defRef . name

mutual
  makeSubSchema : TDef 0 -> JSON
  makeSubSchema  T0         = defRef "emptyType"
  makeSubSchema  T1         = defRef "singletonType"
  makeSubSchema (TSum ts)   = disjointSubSchema (zip (nary "case") ts)
  makeSubSchema (TProd ts)  = productSubSchema (nary "proj") ts
  makeSubSchema (TMu cs)    = defRef (nameMu cs)
  makeSubSchema (TApp f []) = defRef . name $ f
  makeSubSchema (TApp f xs) = defRef . name $ f `apN` xs
  
  ||| Generate a schema that matches exactly one of the supplied schemas, which must be wrapped in its corresponding name.
  disjointSubSchema : Vect k (Name, TDef 0) -> JSON
  disjointSubSchema cases = JObject [("oneOf", JArray . toList $ map makeCase cases)]
    where
    isMu : TDef n -> Bool
    isMu (TMu _) = True
    isMu _       = False

    makeCase : (Name, TDef 0) -> JSON
    makeCase (name, td) = JObject
      [ ("type", JString "object")
      , ("required", JArray [JString name])
      , ("additionalProperties", JBoolean False)
      , ("properties", JObject [(name, assert_total $ makeSubSchema td)])
      ]

  ||| Generate a schema that requires all of the supplied schemas to match, with each being wrapped in its corresponding name.
  productSubSchema : Vect k Name -> Vect k (TDef 0) -> JSON
  productSubSchema names tds = JObject
    [ ("type", JString "object")
    , ("required", JArray . toList $ map JString names)
    , ("additionalProperties", JBoolean False)
    , ("properties", JObject . toList $ Vect.zip names (map (assert_total makeSubSchema) tds))
    ]

mutual
  ||| Generate helper definitions for all types contained in a `TDef 0`.
  makeDefs : TDef 0 -> State (List Name) (List JSONDef)
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

  makeDefs    (TSum ts)   = concat <$> traverse (assert_total makeDefs) ts
  makeDefs    (TProd ts)  = concat <$> traverse (assert_total makeDefs) ts
  makeDefs td@(TMu cases) = makeDefs' (TName (nameMu cases) td)
  makeDefs    (TApp f []) = makeDefs' f
  makeDefs    (TApp f xs) = makeDefs' (f `apN` xs)

  makeDefs' : TNamed 0 -> State (List Name) (List JSONDef)
  makeDefs' (TName name body) = ifNotPresent name $
    case body of
      TMu cs => do -- Named `TMu`s are treated specially
        let cases = map (map (flattenMus name)) cs
        res <- concat <$> traverse {b=List JSONDef} (assert_total $ makeDefs . snd) cases
        pure $ (name, disjointSubSchema cases) :: res
      _ => do -- All other named types are treated as synonyms.
        res <- assert_total $ makeDefs body
        pure $ (name, makeSubSchema body) :: res

||| Takes a schema and a list of helper definitions and puts them together into a top-level schema. 
makeSchema : JSON -> List JSONDef -> JSON
makeSchema schema [] = JObject
                  [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                  , ("type", JString "object")
                  , ("required", JArray [JString "value"])
                  , ("additionalProperties", JBoolean False)
                  , ("properties", JObject [ ("value", schema) ])
                  ]
makeSchema schema defs = JObject
                  [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                  , ("type", JString "object")
                  , ("required", JArray [JString "value"])
                  , ("additionalProperties", JBoolean False)
                  , ("definitions", JObject defs)
                  , ("properties", JObject [ ("value", schema) ])
                  ]

generateSchema : TNamed 0 -> JSON
generateSchema tn = makeSchema (makeSubSchema' tn) (evalState (makeDefs' tn) [])

ASTGen JSONDef JSON False where
  msgType (Zero tn) = makeSubSchema' tn
  generateTyDefs tns = 
    evalState (foldlM (\lh,(Zero tn) => (lh ++) <$> (makeDefs' tn)) [] tns) (the (List Name) [])
    --evalState (makeDefs' tn) []
  generateTermDefs tn = [] -- TODO?

CodegenInterdep JSONDef JSON where
  sourceCode msg defs = literal $ format 2 $ makeSchema msg defs
