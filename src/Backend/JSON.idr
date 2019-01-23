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

JSONDef : Type
JSONDef = (Name, JSON)

AbsJSON : (n : Nat) -> Type
AbsJSON n = Vect n JSON -> JSONDef

||| Given `name`, create `[name0, name1, ..., namek]`
nary : Name -> Vect k Name
nary name = map ((name ++) . show . finToNat) range

||| Reference a definition.
defRef : Name -> JSON
defRef name = JObject [("$ref", JString $ "#/definitions/" ++ name)]

anonMu : Vect n (Name, TDef k) -> Name
anonMu = concatMap fst

makeName : TDef n -> Vect n Name -> Name
makeName T0 _ = "emptyType"
makeName T1 _ = "singletonType"
makeName (TApp f xs) args = name f ++ parens (concatMap (flip (assert_total makeName) args) xs)
makeName (TVar v) args = index v args
makeName (TSum ts) args = "sum" ++ parens (concatMap (flip (assert_total makeName) args) ts)
makeName (TProd ts) args = "prod" ++ parens (concatMap (flip (assert_total makeName) args) ts)
makeName (TMu cases) args = "mu" ++ square (anonMu cases) ++ parens (concat args)

make0Name : TDef 0 -> Name
make0Name = flip makeName []
{-
mutual
  ||| Generate a schema for a `TDef 0`. The schema will be unusable without the definitions for the types referenced in the `TDef 0`.
  makeSubSchema : TDef n -> Vect n (TDef 0) -> JSON
  makeSubSchema T0          _    = defRef "emptyType"
  makeSubSchema T1          _    = defRef "singletonType"
  makeSubSchema (TSum ts)   args = disjointSubSchema (zip (nary "case") ts) args
  makeSubSchema (TProd ts)  args = productSubSchema (nary "proj") ts args
  makeSubSchema (TVar v)    args = makeSubSchema (index v args) []
  makeSubSchema (TMu cases) args = disjointSubSchema cases (?hmm :: args)
  makeSubSchema (TApp f xs) args = makeSubSchema' f (map (flip ap args) xs)

  makeSubSchema' : TNamed n -> Vect n (TDef 0) -> JSON
  makeSubSchema' (TName name _) args = defRef $ name ++ concatMap make0Name args

  ||| Generate a schema that matches exactly one of the supplied schemas, which must be wrapped in its corresponding name.
  disjointSubSchema : Vect k (Name, TDef n) -> Vect n (TDef 0) -> JSON
  disjointSubSchema cases args = JObject [("oneOf", JArray . toList $ map (makeCase args) cases)]
    where
    makeCase : Vect n (TDef 0) -> (Name, TDef n) -> JSON
    makeCase argss (name, td) = JObject
      [ ("type", JString "object")
      , ("required", JArray [JString name])
      , ("additionalProperties", JBoolean False)
      , ("properties", JObject [(name, assert_total $ makeSubSchema td argss)])
      ]

  ||| Generate a schema that requires all of the supplied schemas to match, with each being wrapped in its corresponding name.
  productSubSchema : Vect k Name -> Vect k (TDef n) -> Vect n (TDef 0) -> JSON
  productSubSchema names tds args = JObject
    [ ("type", JString "object")
    , ("required", JArray . toList $ map JString names)
    , ("additionalProperties", JBoolean False)
    , ("properties", JObject . toList $ Vect.zip names (map (assert_total $ flip makeSubSchema args) tds))
    ]

make0SubSchema : TDef 0 -> JSON
make0SubSchema = flip makeSubSchema [] 
-}
||| Only perform an action if a name is not already present in the state. If the action is performed, the name will be added.
ifNotPresent : Eq b => b -> State (List b) (List a) -> State (List b) (List a)
ifNotPresent name gen = do
  st <- get
  if name `List.elem` st
    then pure []
    else modify ([name] ++) *> gen
{-
mutual
  makeAbsDefs : TDef n -> Vect n (TDef 0) -> State (List Name) (List JSONDef)
  makeAbsDefs T0             _    = ifNotPresent "emptyType" $ pure [("emptyType", emptyType)]
    where
    emptyType : JSON
    emptyType = JObject 
                [ ("type", JString "array")
                , ("items", JObject [ ("type", JString "boolean") ])
                , ("minItems", JNumber 3)
                , ("uniqueItems", JBoolean True)
                ]
  makeAbsDefs T1             _    = ifNotPresent "singletonType" $ pure [("singletonType", singletonType)]
      where
      singletonType : JSON
      singletonType = JObject [("enum", JArray [JString "singleton"])]
  makeAbsDefs (TSum ts)      args = concat <$> traverse (flip makeAbsDefs args) ts
  makeAbsDefs (TProd ts)     args = concat <$> traverse (flip makeAbsDefs args) ts
  makeAbsDefs td@(TMu cases) args = makeAbsDefs' (TName (anonMu cases) td) args  -- We name anonymous mus using their constructors.
  makeAbsDefs (TVar v)       args = pure [] --[(?nameVar, make0SubSchema $ index v args)]
  makeAbsDefs (TApp f xs)    args = do
    res <- assert_total $ concat <$> traverse (flip makeAbsDefs args) xs
    res' <- makeAbsDefs' f (map (flip ap args) xs)
    pure $ res ++ res'
  
  makeAbsDefs' : TNamed n -> Vect n (TDef 0) -> State (List Name) (List JSONDef)
  makeAbsDefs' (TName name body) args = ifNotPresent name $ do
    case body of
      TMu cases => do
        ?namedMuDefs
      _         => do
        res <- makeAbsDefs body args
        pure $ (name, makeSubSchema body args) :: res
-}
data ApplicationTree = MkAppTree Name (List ApplicationTree)

JSONEnv : Nat -> Type
JSONEnv n = Vect n ApplicationTree

toAppTree : JSONEnv n -> TDef n -> ApplicationTree
toAppTree _   T0          = MkAppTree "emptyType" []
toAppTree _   T1          = MkAppTree "singletonType" []
toAppTree env (TSum ts)   = MkAppTree "sum" (toList $ map (assert_total $ toAppTree env) ts)
toAppTree env (TProd ts)  = MkAppTree "prod" (toList $ map (assert_total $ toAppTree env) ts)
toAppTree env (TVar v)    = index v env
toAppTree env (TMu cases) = MkAppTree (anonMu cases) (toList env) -- TODO getUsedVars
toAppTree env (TApp f xs) = MkAppTree (name f) (toList env) -- TODO getUsedVars

appTreeToName : ApplicationTree -> Name
appTreeToName (MkAppTree f xs) = f ++ parens (concatMap (assert_total appTreeToName) xs)

makeNameWithEnv' : JSONEnv n -> TNamed n -> Name
makeNameWithEnv' env (TName name _) = name ++ parens (concatMap appTreeToName env) -- TODO getUsedVars

entryToName : Either Name Decl -> Name
entryToName (Left n) = n
entryToName (Right (MkDecl n xs)) = n ++ parens (concat xs) -- TODO comma separation

makeNameWithEnv : JSONEnv n -> TDef n -> Name
makeNameWithEnv env td = appTreeToName (toAppTree env td)

--makeNameWithEnv : JSONEnv n -> TDef n -> Name
--makeNameWithEnv _      T0          = "emptyType"
--makeNameWithEnv _      T1          = "singletonType"
--makeNameWithEnv env    (TSum ts)   = "sum" ++ parens (concatMap (assert_total $ makeNameWithEnv env) ts)
--makeNameWithEnv env    (TProd ts)  = "prod" ++ parens (concatMap (assert_total $ makeNameWithEnv env) ts)
--makeNameWithEnv env    (TVar v)    = appTreeToName (index v env)
--makeNameWithEnv env td@(TMu cases) = makeNameWithEnv' env (TName (anonMu cases) td)
--makeNameWithEnv env    (TApp f xs) = makeNameWithEnv' (map (toAppTree env) xs) f

mutual
  makeSSwithEnv' : JSONEnv n -> TNamed n -> JSON
  makeSSwithEnv' env (TName name body) = defRef $ name ++ parens (concatMap appTreeToName env) -- TODO getUsedVars

  makeSSwithEnv : JSONEnv n -> TDef n -> JSON
  makeSSwithEnv _    T0         = defRef "emptyType"
  makeSSwithEnv _    T1         = defRef "singletonType"
  makeSSwithEnv env (TSum ts)   = disjointSSenv env (zip (nary "case") ts)
  makeSSwithEnv env (TProd ts)  = productSSenv env (nary "proj") ts
  makeSSwithEnv env (TVar v)    = defRef . appTreeToName $ index v env
  makeSSwithEnv env (TMu cases) = disjointSSenv (MkAppTree (anonMu cases) (toList env) :: env) cases
  makeSSwithEnv env (TApp f xs) = makeSSwithEnv' (map (toAppTree env) xs) f

  ||| Generate a schema that matches exactly one of the supplied schemas, which must be wrapped in its corresponding name.
  disjointSSenv : JSONEnv n -> Vect k (Name, TDef n) -> JSON
  disjointSSenv env cases = JObject [("oneOf", JArray . toList $ map (makeCase env) cases)]
    where
    makeCase : JSONEnv n -> (Name, TDef n) -> JSON
    makeCase argss (name, td) = JObject
      [ ("type", JString "object")
      , ("required", JArray [JString name])
      , ("additionalProperties", JBoolean False)
      , ("properties", JObject [(name, assert_total $ makeSSwithEnv argss td)])
      ]

  ||| Generate a schema that requires all of the supplied schemas to match, with each being wrapped in its corresponding name.
  productSSenv : JSONEnv n -> Vect k Name -> Vect k (TDef n) -> JSON
  productSSenv env names tds = JObject
    [ ("type", JString "object")
    , ("required", JArray . toList $ map JString names)
    , ("additionalProperties", JBoolean False)
    , ("properties", JObject . toList $ Vect.zip names (map (assert_total $ makeSSwithEnv env) tds))
    ]

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
  makeDefs _      (TVar _)    = pure [] --[(?nameVar, make0SubSchema $ index v env)]
  makeDefs env    (TApp f xs) = do
    res <- concat <$> traverse (assert_total $ makeDefs env) xs
    res' <- makeDefs' (map (toAppTree env) xs) f
    pure $ res ++ res'
  
  makeDefs' : JSONEnv n -> TNamed n -> State (List Name) (List JSONDef)
  makeDefs' env tn@(TName name body) = ifNotPresent (makeNameWithEnv' env tn) $ 
    case body of
      TMu cases => do -- Named `TMu`s are treated specially
        let newEnv = MkAppTree name (toList env) :: env
        res <- concat <$> traverse {b=List JSONDef} (assert_total $ makeDefs newEnv . snd) (cases)
        pure $ (makeNameWithEnv' env tn, disjointSSenv newEnv cases) :: res
      _         => do -- All other named types are treated as synonyms.
        res <- assert_total $ makeDefs env body
        pure $ (makeNameWithEnv' env tn, makeSSwithEnv env body) :: res

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
generateSchema td = makeSchema (makeSSwithEnv' [] td) (evalState (makeDefs' [] td) [])

--NewBackend JSONDef JSON where
--  msgType                    = makeSubSchema
--  typedefs td                = map (uncurry MkJSONDef) $ evalState (makeDefs td) []
--  source topLevelSchema defs = literal $ format 2 $ makeSchema topLevelSchema defs