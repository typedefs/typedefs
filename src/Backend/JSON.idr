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
  makeSchema : TDef n -> JSON
  makeSchema T0             = defRef "emptyType"
  makeSchema T1             = defRef "singletonType"
  makeSchema (TSum ts)      = JObject [("oneOf", JArray . toList $ zipWith tagSchema (nary "case") ts)]
  makeSchema (TProd ts)     = JObject [("allOf", JArray . toList $ zipWith tagSchema (nary "proj") ts)]
  makeSchema (TVar v)       = ?tvarschema
  makeSchema (TName name _) = defRef name
  makeSchema (TMu name _)   = defRef name
  
  tagSchema : Name -> TDef n -> JSON
  tagSchema name t = JObject
                      [ ("type", JString "object")
                      , ("required", JArray [JString name])
                      , ("properties", JObject [(name, assert_total $ makeSchema t)])
                      ]



makeDefs : TDef n -> State (List Name) (List (String, JSON))
makeDefs T0 = pure [("emptyType", emptyType)]
              <* addName "emptyType"
  where
  emptyType : JSON
  emptyType = JObject 
                [ ("type", JString "array")
                , ("items", JObject [ ("type", JString "boolean") ])
                , ("minItems", JNumber 3)
                , ("uniqueItems", JBoolean True)
                ]
makeDefs T1 = pure [("singletonType", singletonType)]
              <* addName "singletonType"
  where
  singletonType : JSON
  singletonType = JObject [("enum", JArray [JString "singleton"])]
makeDefs (TSum ts)        = map concat $ traverse (assert_total makeDefs) ts
makeDefs (TProd ts)       = map concat $ traverse (assert_total makeDefs) ts
makeDefs (TVar v)         = ?tvardef
makeDefs s@(TName name t) = do
    st <- get
    if name `Prelude.List.elem` st then pure []
    else do
      res <- makeDefs (assert_smaller s t)
      addName name
      pure $ (name, makeSchema t) :: res
makeDefs t@(TMu name cases) = do
    st <- get
    if name `Prelude.List.elem` st then pure []
    else do
      res <- map concat $ traverse (assert_total makeDefs . snd) cases
      addName name
      pure $ (name, ?makeConstructorSchemas cases) :: res