module Test.JSON

import Types
import Typedefs

import Backend
import Backend.Utils
import Backend.JSON

import Language.JSON

import Text.PrettyPrint.WL
import Specdris.Spec

import Data.Vect
import Test

%access public export

generate : TNamed 0 -> Doc
generate = generate JSONDef

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

voidOrUnitDef : Doc
voidOrUnitDef = dquotes "VoidOrUnit" |+| colon |++| sumDef [ref "emptyType", unitRef]

generalDoc : Doc -> List Doc -> Doc
generalDoc top defs = subthing braces
  [ dquotes "$schema"              |+| colon |++| dquotes "http://json-schema.org/draft-07/schema#"
  , dquotes "type"                 |+| colon |++| dquotes "object"
  , dquotes "required"             |+| colon |++| subthing brackets [ dquotes "value" ]
  , dquotes "additionalProperties" |+| colon |++| text "false"
  , dquotes "definitions"          |+| colon |++| subthing braces defs
  , dquotes "properties"           |+| colon |++| subthing braces 
    [ dquotes "value" |+| colon |++| top ]
  ]

testSuite : IO ()
testSuite = spec $ do

  describe "JSON code generation tests:" $ do

    it "bit" $
      generate bit
        `shouldBe` generalDoc (ref "Bit") [bitDef, unitDef]

    it "byte" $
      generate byte
        `shouldBe` generalDoc (ref "Byte") [byteDef, bitDef, unitDef]

    it "nat" $
      generate nat
        `shouldBe` generalDoc (ref "Nat") [natDef, unitDef]

    it "listNat" $
      generate listNat
        `shouldBe` generalDoc (ref "ListNat") [listNatDef, unitDef, natDef]

    it "oneoneoneone" $
      generate oneoneoneone
        `shouldBe` generalDoc (ref "oneoneoneone") [oneoneoneoneDef, unitDef]

    it "void or unit" $
      generate voidOrUnit
        `shouldBe` generalDoc (ref "VoidOrUnit") [voidOrUnitDef, voidDef, unitDef]
