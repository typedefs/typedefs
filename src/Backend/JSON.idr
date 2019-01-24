module Backend.JSON

import Types
import Typedefs

import Backend
import Backend.Utils

import Control.Monad.State
import Language.JSON
import Text.PrettyPrint.WL

import Data.Vect

%default total
%access public export

data ApplicationTree = AppTree Name (List ApplicationTree)

JSONEnv : Nat -> Type
JSONEnv n = Vect n (ApplicationTree, JSON)

JSONDef : Type
JSONDef = (Name, JSON)

||| Given `name`, create `[name0, name1, ..., namek]`
nary : Name -> Vect k Name
nary name = map ((name ++) . show . finToNat) range

||| Reference a definition.
defRef : Name -> JSON
defRef name = JObject [("$ref", JString $ "#/definitions/" ++ name)]

anonMu : Vect n (Name, TDef k) -> Name
anonMu = concatMap fst

||| Only perform an action if a name is not already present in the state. If the action is performed, the name will be added.
ifNotPresent : Eq name => name -> State (List name) (List def) -> State (List name) (List def)
ifNotPresent n gen = do
  st <- get
  if n `List.elem` st
    then pure []
    else modify {stateType=List name} (n ::) *> gen

toAppTree : JSONEnv n -> TDef n -> ApplicationTree
toAppTree _   T0          = AppTree "emptyType" []
toAppTree _   T1          = AppTree "singletonType" []
toAppTree env (TSum ts)   = AppTree "sum" (toList $ map (assert_total $ toAppTree env) ts)
toAppTree env (TProd ts)  = AppTree "prod" (toList $ map (assert_total $ toAppTree env) ts)
toAppTree env (TVar v)    = fst $ index v env
toAppTree env (TMu cases) = AppTree (anonMu cases) (toList $ map fst env) -- TODO getUsedVars
toAppTree env (TApp f xs) = AppTree (name f) (toList $ map fst env) -- TODO getUsedVars

appTreeToName : ApplicationTree -> Name
appTreeToName (AppTree f xs) = f ++ parens (concatMap (assert_total appTreeToName) xs) -- TODO comma separation

makeNameWithEnv' : JSONEnv n -> TNamed n -> Name
makeNameWithEnv' env (TName name _) = name ++ parens (concatMap (appTreeToName . fst) env) -- TODO getUsedVars

makeNameWithEnv : JSONEnv n -> TDef n -> Name
makeNameWithEnv env td = appTreeToName (toAppTree env td)

mutual
  makeSubSchema' : JSONEnv n -> TNamed n -> JSON
  makeSubSchema' env (TName name body) = defRef $ name ++ parens (concatMap (appTreeToName . fst) env) -- TODO getUsedVars

  makeSubSchema : JSONEnv n -> TDef n -> JSON
  makeSubSchema _    T0         = defRef "emptyType"
  makeSubSchema _    T1         = defRef "singletonType"
  makeSubSchema env (TSum ts)   = disjointSubSchema env (zip (nary "case") ts)
  makeSubSchema env (TProd ts)  = productSubSchema env (nary "proj") ts
  makeSubSchema env (TVar v)    = defRef . appTreeToName . fst $ index v env
  makeSubSchema env (TMu cases) = let appTree = AppTree (anonMu cases) (toList $ map fst env)
                                   in disjointSubSchema ((appTree, defRef $ appTreeToName appTree) :: env) cases
  makeSubSchema env (TApp f xs) = makeSubSchema' (map (\td => (toAppTree env td, JString "oh no :/")) xs) f

  ||| Generate a schema that matches exactly one of the supplied schemas, which must be wrapped in its corresponding name.
  disjointSubSchema : JSONEnv n -> Vect k (Name, TDef n) -> JSON
  disjointSubSchema env cases = JObject [("oneOf", JArray . toList $ map (makeCase env) cases)]
    where
    makeCase : JSONEnv n -> (Name, TDef n) -> JSON
    makeCase argss (name, td) = JObject
      [ ("type", JString "object")
      , ("required", JArray [JString name])
      , ("additionalProperties", JBoolean False)
      , ("properties", JObject [(name, assert_total $ makeSubSchema argss td)])
      ]

  ||| Generate a schema that requires all of the supplied schemas to match, with each being wrapped in its corresponding name.
  productSubSchema : JSONEnv n -> Vect k Name -> Vect k (TDef n) -> JSON
  productSubSchema env names tds = JObject
    [ ("type", JString "object")
    , ("required", JArray . toList $ map JString names)
    , ("additionalProperties", JBoolean False)
    , ("properties", JObject . toList $ Vect.zip names (map (assert_total $ makeSubSchema env) tds))
    ]

--TDefEnv : Nat -> Type
--TDefEnv n = Vect n (All TNamed)

mutual
  ||| Generate helper definitions for all types contained in a `TDef 0`.
  makeDefs : JSONEnv n -> TDef n -> State (List Name) (List JSONDef)
  makeDefs _ T0 = ifNotPresent "emptyType" $ pure [("emptyType", emptyType)]
    where
    emptyType : JSON
    emptyType = JObject 
                [ ("type", JString "array")
                , ("items", JObject [ ("type", JString "boolean") ])
                , ("minItems", JNumber 3)
                , ("uniqueItems", JBoolean True)
                ]
  makeDefs _ T1 = ifNotPresent "singletonType" $ pure [("singletonType", singletonType)]
      where
      singletonType : JSON
      singletonType = JObject [("enum", JArray [JString "singleton"])]

  makeDefs env    (TSum ts)   = concat <$> traverse (assert_total $ makeDefs env) ts
  makeDefs env    (TProd ts)  = concat <$> traverse (assert_total $ makeDefs env) ts
  makeDefs env td@(TMu cases) = makeDefs' env (TName (anonMu cases) td)  -- We name anonymous mus using their constructors.
  makeDefs env    (TVar v)    = let (appTree, json) = index v env
                                 in ifNotPresent (appTreeToName appTree)
                                  $ pure [(appTreeToName appTree, json)]
  makeDefs env    (TApp f xs) = do
    res <- concat <$> traverse (assert_total $ makeDefs env) xs
    res' <- makeDefs' (map (\td => (toAppTree env td, makeSubSchema env td)) xs) f
    pure $ res ++ res'

  makeDefs' : JSONEnv n -> TNamed n -> State (List Name) (List JSONDef)
  makeDefs' env tn@(TName name body) = ifNotPresent (makeNameWithEnv' env tn) $ 
    case body of
      TMu cases => do -- Named `TMu`s are treated specially
        let appTree = AppTree name (toList $ map fst env)
        let newEnv = (appTree, defRef (appTreeToName appTree)) :: env
        res <- concat <$> traverse {b=List JSONDef} (assert_total $ makeDefs newEnv . snd) cases
        pure $ (makeNameWithEnv' env tn, disjointSubSchema newEnv cases) :: res
      _         => do -- All other named types are treated as synonyms.
        res <- assert_total $ makeDefs env body
        pure $ (makeNameWithEnv' env tn, makeSubSchema env body) :: res

||| Takes a schema and a list of helper definitions and puts them together into a top-level schema. 
makeSchema : JSON -> List JSONDef -> JSON
makeSchema schema defs = JObject
                  [ ("$schema", JString "http://json-schema.org/draft-07/schema#")
                  , ("type", JString "object")
                  , ("required", JArray [JString "value"])
                  , ("additionalProperties", JBoolean False)
                  , ("definitions", JObject defs)
                  , ("properties", JObject [ ("value", schema) ])
                  ]

generateSchema : TNamed 0 -> JSON
generateSchema td = makeSchema (makeSubSchema' [] td) (evalState (makeDefs' [] td) [])

--NewBackend JSONDef JSON where
--  msgType                    = makeSubSchema
--  typedefs td                = map (uncurry MkJSONDef) $ evalState (makeDefs td) []
--  source topLevelSchema defs = literal $ format 2 $ makeSchema topLevelSchema defs