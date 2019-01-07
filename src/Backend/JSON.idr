module Backend.JSON

import Control.Monad.State
import Language.JSON
import Text.PrettyPrint.WL

import Backend
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


record JSONDef where
  constructor MkJSONDef
  name   : Name
  schema : JSON

mutual
  makeSubSchema : TDef 0 -> JSON
  makeSubSchema T0             = defRef "emptyType"
  makeSubSchema T1             = defRef "singletonType"
  makeSubSchema (TSum ts)      = disjointSubSchema $ zip (nary "case") ts
  makeSubSchema (TProd ts)     = productSubSchema (nary "proj") ts
  makeSubSchema (TName name _) = defRef name
  makeSubSchema (TMu name _)   = defRef name
  
  disjointSubSchema : Vect k (Name, TDef 0) -> JSON
  disjointSubSchema cases = JObject [("oneOf", JArray . toList $ map makeCase cases)]
    where makeCase : (Name, TDef 0) -> JSON
          makeCase (name, td) = JObject
                                  [ ("type", JString "object")
                                  , ("required", JArray [JString name])
                                  , ("additionalProperties", JBoolean False)
                                  , ("properties", JObject [(name, assert_total $ makeSubSchema td)])
                                  ]

  productSubSchema : Vect k Name -> Vect k (TDef 0) -> JSON
  productSubSchema names tds = JObject
                                 [ ("type", JString "object")
                                 , ("required", JArray . toList $ map JString names)
                                 , ("additionalProperties", JBoolean False)
                                 , ("properties", JObject . toList $ zip names (map (assert_total makeSubSchema) tds))
                                 ]

ifNotPresent : Name -> State (List Name) (List (String, JSON)) -> State (List Name) (List (String, JSON))
ifNotPresent name gen = do
    st <- get
    if name `Prelude.List.elem` st
      then pure []
      else addName name *> gen

makeDefs : TDef 0 -> State (List Name) (List (String, JSON))
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
makeDefs s@(TName name t) = ifNotPresent name $ do
    res <- makeDefs (assert_smaller s t)
    pure $ (name, makeSubSchema t) :: res
makeDefs t@(TMu name cases) = ifNotPresent name $ do
    let cases' = map (map (flattenMu [name])) cases
    res <- map concat $ traverse (assert_total makeDefs . snd) cases'
    pure $ (name, disjointSubSchema cases') :: res
  where
  -- DO NOT simply lift this function out to the top-level.
  -- Its behavior is dependent on the type of `makeDefs`.
  -- (Specifically: all TVars must refer to a TMu, not to any free variables.)
  flattenMu : Vect (S n) Name -> TDef (S n) -> TDef n
  flattenMu names (TVar v)    = TName (index v names) T0
  flattenMu _     T0          = T0
  flattenMu _     T1          = T1
  flattenMu names (TSum ts)   = assert_total $ TSum $ map (flattenMu names) ts
  flattenMu names (TProd ts)  = assert_total $ TProd $ map (flattenMu names) ts
  flattenMu names (TName n t) = assert_total $ TName n $ flattenMu names t
  flattenMu names (TMu n c)   = assert_total $ TMu n $ map (map (flattenMu (n :: names))) c

makeSchema : JSON -> List JSONDef -> JSON
makeSchema schema defs = JObject
                  [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                  , ("type", JString "object")
                  , ("required", JArray [JString "value"])
                  , ("additionalProperties", JBoolean False)
                  , ("definitions", jObject defs)
                  , ("properties", JObject [ ("value", schema) ])
                  ]
  where
  jObject : List JSONDef -> JSON
  jObject = JObject . map (\(MkJSONDef name def) => (name, def))

--Backend JSONDef where
--  generateTyDefs td = map (uncurry MkJSONDef) $ evalState (makeDefs td) []
--  generateCode (MkJSONDef name schema) = format 0 schema
--  generate td defs = format 0 $ makeSchema td defs

NewBackend JSON JSONDef where
  tld = makeSubSchema
  defs td = map (uncurry MkJSONDef) $ evalState (makeDefs td) []
  source topLevelSchema defs = literal $ format 0 $ makeSchema topLevelSchema defs

