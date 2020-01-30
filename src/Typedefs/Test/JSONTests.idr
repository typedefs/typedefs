module Typedefs.Test.JSONTests

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.Backend
import Typedefs.Backend.Utils
import Typedefs.Backend.JSON

import Typedefs.Test

import Language.JSON

import Text.PrettyPrint.WL
import Specdris.Spec

import Data.NEList
import Data.Vect

%access public export

generate : TNamedR 0 -> Maybe Doc
generate tn = Backend.generate JSONDef $ singleton (Z ** tn)

dquotes : String -> Doc
dquotes = dquotes . text

subthing : (Doc -> Doc) -> List Doc -> Doc
subthing enclose docs = enclose (line |+| (vsep $ map (indent 2) (punctuate comma docs)) |+| line)

ref : String -> Doc
ref name = subthing braces [ dquotes "$ref" |+| colon |++| dquotes ("#/definitions/" ++ name) ]

unitRef : Doc
unitRef = ref "singletonType"

unitDef : Doc
unitDef = dquotes "singletonType" |+| colon |++| subthing braces
            [ dquotes "enum" |+| colon |++| subthing brackets [ dquotes "singleton" ] ]

voidDef : Doc
voidDef = dquotes "emptyType" |+| colon |++| subthing braces
            [ dquotes "type" |+| colon |++| dquotes "array"
            , dquotes "items" |+| colon |++| subthing braces [ dquotes "type" |+| colon |++| dquotes "boolean" ]
            , dquotes "minItems" |+| colon |++| text "3"
            , dquotes "uniqueItems" |+| colon |++| text "true"
            ]

taggedSumDef : List (String, Doc) -> Doc
taggedSumDef ds = subthing braces [ dquotes "oneOf" |+| colon |++| subthing brackets (map f ds) ]
  where
  f : (String, Doc) -> Doc
  f (tag,d) = let inj = dquotes tag
              in subthing braces
                  [ dquotes "type"                 |+| colon |++| dquotes "object"
                  , dquotes "required"             |+| colon |++| subthing brackets [ inj ]
                  , dquotes "additionalProperties" |+| colon |++| text "false"
                  , dquotes "properties"           |+| colon |++| subthing braces
                    [ inj |+| colon |++| d ]
                  ]

sumDef : List Doc -> Doc
sumDef ds = taggedSumDef (zip (map (\ix => "case" ++ show ix) [0 .. length ds]) ds)

prodDef : List Doc -> Doc
prodDef ds = let projs = map (\ix => dquotes ("proj" ++ show ix)) (fromMaybe [] $ init' [0 .. length ds])
              in subthing braces
                  [ dquotes "type" |+| colon |++| dquotes "object"
                  , dquotes "required" |+| colon |++| subthing brackets projs
                  , dquotes "additionalProperties" |+| colon |++| text "false"
                  , dquotes "properties" |+| colon |++| subthing braces (zipWith f projs ds)
                  ]
  where
  f : Doc -> Doc -> Doc
  f p d = p |+| colon |++| d

bitDef : Doc
bitDef = dquotes "Bit" |+| colon |++| sumDef [ unitRef, unitRef ]

byteDef : Doc
byteDef = dquotes "Byte" |+| colon |++| prodDef (replicate 8 $ ref "Bit")

natDef : Doc
natDef = dquotes "Nat" |+| colon |++| taggedSumDef [ ("Z", unitRef), ("S", ref "Nat") ]

listNatDef : Doc
listNatDef = dquotes "ListNat" |+| colon |++| taggedSumDef [ ("NilN", unitRef), ("ConsN", prodDef [ref "Nat", ref "ListNat"]) ]

oneoneoneoneDef : Doc
oneoneoneoneDef = dquotes "oneoneoneone" |+| colon |++| sumDef (replicate 4 unitRef)

listByteDef : Doc
listByteDef = dquotes "ListByte" |+| colon |++| taggedSumDef [ ("NilC", unitRef), ("ConsC", prodDef [ref "Byte", ref "ListByte"]) ]

voidOrUnitDef : Doc
voidOrUnitDef = dquotes "VoidOrUnit" |+| colon |++| sumDef [ref "emptyType", unitRef]

listBitOrByteDefs : List Doc
listBitOrByteDefs = [ dquotes "listBitOrByte" |+| colon |++| ref "listAlphaOrBeta(Bit,Byte)"
                    , appliedParametric
                    , unitDef
                    , bitDef
                    , byteDef
                    ]
  where
  appliedParametric = dquotes "listAlphaOrBeta(Bit,Byte)" |+| colon
               |++| taggedSumDef [ ("Nil", unitRef)
                                 , ("Cons", prodDef [ sumDef [ ref "Bit"
                                                             , ref "Byte"]
                                                    , ref "listAlphaOrBeta(Bit,Byte)"]) ]

nestedMu3Defs : List Doc
nestedMu3Defs = [ dquotes "nestedMu3" |+| colon
                  |++| taggedSumDef [("Foobar", ref "Maybe2(nestedMu3)")]
                , appliedMaybe2
                , unitDef
                ]
  where
  appliedMaybe2 : Doc
  appliedMaybe2 = dquotes "Maybe2(nestedMu3)" |+| colon
                  |++| taggedSumDef [ ("Nothing", unitRef)
                                    , ("Just", ref "nestedMu3") ]

nestedMu5Defs : List Doc
nestedMu5Defs = [ dquotes "nestedMu5" |+| colon
                  |++| taggedSumDef [("Foobar", ref "NilCons")]
                , appliedNilCons
                , unitDef
                ]
  where
  appliedNilCons : Doc
  appliedNilCons = dquotes "NilCons" |+| colon
            |++| taggedSumDef [ ("Nil", unitRef)
                              , ("Cons", prodDef [ref "nestedMu5", ref "NilCons"]) ]

listOfDefsJSON : List Doc
listOfDefsJSON = [ dquotes "bit"          |+| colon |++| sumDef [ unitRef, unitRef ]
                 , unitDef
                 , dquotes "nibble"       |+| colon |++| prodDef (replicate 4 $ ref "bit")
                 , dquotes "byte"         |+| colon |++| prodDef (replicate 2 $ ref "nibble")
                 , dquotes "char"         |+| colon |++| ref "byte"
                 , dquotes "hash"         |+| colon |++| ref "byte"
                 , dquotes "transitionId" |+| colon |++| ref "byte"
                 , dquotes "data"         |+| colon |++| ref "byte"
                 , dquotes "previous"     |+| colon |++| ref "hash"
                 , dquotes "rootTx"       |+| colon |++| prodDef [ref "data", ref "previous"]
                 ]

generalDoc : List Doc -> List Doc -> Doc
generalDoc types defs = subthing braces
  [ dquotes "$schema"              |+| colon |++| dquotes "http://json-schema.org/draft-07/schema#"
  , dquotes "type"                 |+| colon |++| dquotes "object"
  , dquotes "required"             |+| colon |++| subthing brackets [ dquotes "value" ]
  , dquotes "additionalProperties" |+| colon |++| text "false"
  , dquotes "definitions"          |+| colon |++| subthing braces defs
  , dquotes "properties"           |+| colon |++| subthing braces
    [ dquotes "value" |+| colon |++| subthing braces [dquotes "oneOf" |+| colon |++| subthing brackets types] ]
  ]

testSuite : IO ()
testSuite = spec $ do

  describe "JSON code generation tests:" $ do

    it "bit" $
      generate bit
        `shouldBe` (Just $ generalDoc [ref "Bit"] [bitDef, unitDef])

    it "byte" $
      generate byte
        `shouldBe` (Just $ generalDoc [ref "Byte"] [byteDef, bitDef, unitDef])

    it "nat" $
      generate nat
        `shouldBe` (Just $ generalDoc [ref "Nat"] [natDef, unitDef])

    it "listNat" $
      generate listNat
        `shouldBe` (Just $ generalDoc [ref "ListNat"] [listNatDef, unitDef, natDef])

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` (Just $ generalDoc [ref "oneoneoneone"] [oneoneoneoneDef, unitDef])

    it "listByte" $
      generate listByte
        `shouldBe` (Just $ generalDoc [ref "ListByte"] [listByteDef, unitDef, byteDef, bitDef])

    it "void or unit" $
      generate voidOrUnit
        `shouldBe` (Just $ generalDoc [ref "VoidOrUnit"] [voidOrUnitDef, voidDef, unitDef])

    it "listBitOrByte" $
      generate listBitOrByte
        `shouldBe` (Just $ generalDoc [ref "listBitOrByte"] listBitOrByteDefs)

    it "nested Mu 3: Maybe2(Mu)" $
      generate nestedMu3
        `shouldBe` (Just $ generalDoc [ref "nestedMu3"] nestedMu3Defs)

    it "nested mu 5: AnonList(Mu)" $
      generate nestedMu5
        `shouldBe` (Just $ generalDoc [ref "nestedMu5"] nestedMu5Defs)

    it "list of definitions [bit, nibble, byte, char, hash, transitionId, data, previous, rootTx]" $
      generate JSONDef listOfDefs
        `shouldBe` (Just $ generalDoc [ ref "bit"
                                      , ref "nibble"
                                      , ref "byte"
                                      , ref "char"
                                      , ref "hash"
                                      , ref "transitionId"
                                      , ref "data"
                                      , ref "previous"
                                      , ref "rootTx"]
                                      listOfDefsJSON)
