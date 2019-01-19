module Backend.NewJSON

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

mutual
  ||| Generate a schema for a `TDef 0`. The schema will be unusable without the definitions for the types referenced in the `TDef 0`.
  makeSubSchema : TDef n -> Vect n JSON -> JSON
  makeSubSchema T0 _ = defRef "emptyType"
  makeSubSchema T1 _ = defRef "singletonType"
  makeSubSchema (TSum ts) args = disjointSubSchema (zip (nary "case") ts) args
  makeSubSchema (TProd ts) args = productSubSchema (nary "proj") ts args
  makeSubSchema (TVar v) args = index v args
  makeSubSchema (TMu cases) args = disjointSubSchema cases (defRef (anonMu cases) :: args)
  makeSubSchema (TApp f xs) args = makeSubSchema' f (map (assert_total $ flip makeSubSchema args) xs)

  makeSubSchema' : TNamed n -> Vect n JSON -> JSON
  makeSubSchema' (TName name _) args = defRef $ name ++ ?makeName args

  ||| Generate a schema that matches exactly one of the supplied schemas, which must be wrapped in its corresponding name.
  disjointSubSchema : Vect k (Name, TDef n) -> Vect n JSON -> JSON
  disjointSubSchema cases args = JObject [("oneOf", JArray . toList $ map (makeCase args) cases)]
    where makeCase : Vect n JSON -> (Name, TDef n) -> JSON
          makeCase argss (name, td) = JObject
                                    [ ("type", JString "object")
                                    , ("required", JArray [JString name])
                                    , ("additionalProperties", JBoolean False)
                                    , ("properties", JObject [(name, assert_total $ makeSubSchema td argss)])
                                    ]

  ||| Generate a schema that requires all of the supplied schemas to match, with each being wrapped in its corresponding name.
  productSubSchema : Vect k Name -> Vect k (TDef n) -> Vect n JSON -> JSON
  productSubSchema names tds args = JObject
                                  [ ("type", JString "object")
                                  , ("required", JArray . toList $ map JString names)
                                  , ("additionalProperties", JBoolean False)
                                  , ("properties", JObject . toList $ Vect.zip names (map (assert_total $ flip makeSubSchema args) tds))
                                  ]

||| Only perform an action if a name is not already present in the state. If the action is performed, the name will be added.
ifNotPresent : Eq b => b -> State (List (b, c)) (List a) -> State (List (b, c)) (List a)
ifNotPresent name gen = do
  st <- get
  if ?condition --name `List.elem` (map fst st)
    then ?true --pure []
    else ?false --?insertName *> gen

makeAbsDefs : TDef n -> State (List JSONDef) (Vect n JSON -> JSON)
makeAbsDefs T0 = pure $ const ?voidDef
makeAbsDefs (TVar v) = pure (index v)

makeAbsDefs' : TNamed n -> State (List JSONDef) (Vect n JSON -> JSONDef)
makeAbsDefs' (TName name body) = do
    res <- makeAbsDefs body
    pure $ \args => (name, makeSubSchema body args)

mutual
  ||| Generate helper definitions for all types contained in a `TDef 0`.
  makeDefs : TDef 0 -> State (List JSONDef) (List JSONDef)
  makeDefs T0 = ifNotPresent "emptyType" $ pure [("emptyType", ?emptyType)]
  makeDefs td@(TMu cases) = makeDefs' $ TName (anonMu cases) td
  makeDefs (TSum ts) = assert_total $ concat <$> traverse makeDefs ts
  makeDefs (TApp f xs) = do
    res <- assert_total $ concat <$> traverse makeDefs xs
    paramDefs <- makeAbsDefs' f
    pure $ paramDefs (map (flip makeSubSchema []) xs) :: res
  
  makeDefs' : TNamed 0 -> State (List JSONDef) (List JSONDef)
  makeDefs' (TName name body) = ifNotPresent name $
    case body of
      TMu cases => ?help
      _         => do
          res <- assert_total $ makeDefs body
          pure $ (name, makeSubSchema body []) :: res

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

--NewBackend JSONDef JSON where
--  msgType                    = makeSubSchema
--  typedefs td                = map (uncurry MkJSONDef) $ evalState (makeDefs td) []
--  source topLevelSchema defs = literal $ format 2 $ makeSchema topLevelSchema defs