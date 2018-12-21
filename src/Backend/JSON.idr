module Backend.JSON

import Control.Monad.State
import Language.JSON
import Text.PrettyPrint.WL

import Backend.Utils
import Types
import Typedefs

import Data.Vect

%default total
%access public export

addName : Name -> State (List Name) ()
addName name = modify ([name] ++)

nary : Name -> Vect k Name
nary name = map ((name ++) . show . finToNat) range

defRef : Name -> JSON
defRef name = JObject [("$ref", JString $ "#/definitions/" ++ name)]

mutual
  makeSubSchema : TDef n -> JSON
  makeSubSchema T0             = defRef "emptyType"
  makeSubSchema T1             = defRef "singletonType"
  makeSubSchema (TSum ts)      = JObject [("oneOf", JArray . toList $ zipWith tagSchema (nary "case") ts)]
  makeSubSchema (TProd ts)     = JObject [("allOf", JArray . toList $ zipWith tagSchema (nary "proj") ts)]
  makeSubSchema (TVar v)       = ?tvarschema
  makeSubSchema (TName name _) = defRef name
  makeSubSchema (TMu name _)   = defRef name
  
  tagSchema : Name -> TDef n -> JSON
  tagSchema name t = JObject
                      [ ("type", JString "object")
                      , ("required", JArray [JString name])
                      , ("properties", JObject [(name, assert_total $ makeSubSchema t)])
                      ]

ifNotPresent : Name -> State (List Name) (List (String, JSON)) -> State (List Name) (List (String, JSON))
ifNotPresent name gen = do
    st <- get
    if name `Prelude.List.elem` st
      then pure []
      else gen <* addName name

makeDefs : TDef n -> State (List Name) (List (String, JSON))
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
makeDefs (TSum ts)        = map concat $ traverse (assert_total makeDefs) ts
makeDefs (TProd ts)       = map concat $ traverse (assert_total makeDefs) ts
makeDefs (TVar v)         = ?tvardef
makeDefs s@(TName name t) = ifNotPresent name $ do
    res <- makeDefs (assert_smaller s t)
    addName name
    pure $ (name, makeSubSchema t) :: res
makeDefs t@(TMu name cases) = ifNotPresent name $ do
    res <- map concat $ traverse (assert_total makeDefs . snd) cases
    addName name
    pure $ (name, makeConstructorSchemas cases) :: res
  where
  makeConstructorSchemas : Vect k (Name, TDef n) -> JSON
  makeConstructorSchemas cons = JObject [ ("oneOf", JArray . toList $ map (uncurry tagSchema) cons) ]

makeSchema : TDef n -> JSON
makeSchema td = let defs = JObject $ evalState (makeDefs td) [] in
                let props = JObject [ ("value", makeSubSchema td)
                                    , ("vars", JObject [])
                                    ]
                 in JObject
                      [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                      , ("type", JString "object")
                      , ("required", JArray [JString "value", JString "vars"]) -- TODO only require vars if 
                      , ("additionalProperties", JBoolean False)
                      , ("definitions", defs)
                      , ("properties", props)
                      ]