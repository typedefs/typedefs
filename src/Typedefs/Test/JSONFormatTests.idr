module Typedefs.Test.JSONFormatTests

import Typedefs.Idris
import Typedefs.Library
import Typedefs.TermParse
import Typedefs.TermWrite

import Data.Vect
import Data.Bytes
import Data.ByteArray
import TParsec
import Specdris.Spec

import Language.JSON

%access public export
%default total

roundtrip1 : (td : TDefR 0) -> Ty [] td -> JSONM (Ty [] td)
roundtrip1 td x = deserialise {format=JSON} {m=Either String} [] td $ serialise  [] [] td x

shouldBeRoundtrip1 : (td : TDefR 0) -> (Show (Ty [] td), Eq (Ty [] td)) => Ty [] td -> SpecResult
shouldBeRoundtrip1 td term = (roundtrip1 td term) `shouldBe` (pure term)

roundtrip2 : (td : TDefR 0) -> JSON -> JSONM JSON
roundtrip2 td x = serialise [] [] td <$> deserialise [] td x

Eq JSON where
  (JNumber a) == (JNumber b) = a == b
  JNull == JNull = True
  (JBoolean a) == (JBoolean b) =  a == b
  (JString a) == (JString b) = a == b
  (JArray a) == (JArray b) = assert_total $ a == b
  (JObject a) == (JObject b) = assert_total $ a == b
  _ == _ = False

-- helper functions to keep me sane while writing the tests
jpair : (a, b : JSON) -> JSON
jpair a b = JObject [("_0", a), ("_1", b)]

jright : JSON -> JSON
jright a = JObject [("_1", a)]

jleft : JSON -> JSON
jleft a = JObject [("_0", a)]

jinn : JSON -> JSON
jinn a = JObject [("inn", a)]

junit : JSON
junit = JObject []

testSuite : IO ()
testSuite = spec $ do

  describe "TermWrite" $ do

    it "serialise unit" $
      (serialise [] [] T1 ()) `shouldBe` junit

    it "serialise sum" $
      (serialise [] [] (TSum [T1, T1]) (Left ())) `shouldBe` jleft junit

    it "serialise prod with var" $
      (serialise [] [JNumber] (TProd [T1, TVar 0]) ((), 2)) `shouldBe`
        (jpair junit (JNumber 2))

    it "serialise mu" $
      (serialise [] [JNumber] (TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])])
        (Inn $ Right (1, Inn $ Right (2, Inn $ Left ()))))
      `shouldBe`
        (jinn $ jright $ jpair (JNumber 1)
                               (jinn $ jright $ jpair (JNumber 2) (jinn $ jleft $ JObject [])))
    it "serialise mu step" $
      (serialise [] []
          (TMu [("Nil", T1),
                ("Cons", TProd [(TMu [("Z", T1),
                                      ("S", TVar 0)]), TVar 0])])
         (Inn (Right
          ( Inn (Left ())
          , Inn (Right
             ( Inn (Right (Inn (Left ())))
             , Inn (Right
                 ( Inn (Right (Inn (Right (Inn (Left ())))))
                 , Inn (Left ())
                 ))
             ))
          ))))
      `shouldBe`
        (jinn (jright (jpair
            (jinn (jleft junit))
            (jinn (jright (jpair
                (jinn (jright (jinn (jleft junit))))
                (jinn (jright (jpair
                    (jinn (jright (jinn (jright (jinn (jleft junit))))))
                    (jinn (jleft junit))
                    )))
                )))
            )))

  describe "TermParse" $ do

    it "deserialise unit" $
      (deserialise [] T1 (JObject [])) `shouldBe` (Right ())

    it "deserialise sum" $
      (deserialise [] (TSum [T1, T1]) (JObject [("_0", JObject [])])) `shouldBe` (Right $ Left ())

    it "deserialise prod with var" $
      (deserialise [parseInt] (TProd [T1, TVar 0]) (jpair (JObject []) (JNumber 2)))
      `shouldBe` (Right ((), 2))

    it "deserialise mu" $
      (deserialise [] (TMu [("Nil", T1), ("Cons", TProd [T1, TVar 0])])
        (jinn $ jright $ jpair (JObject [])
                               (jinn $ jright $ jpair (JObject [])
                                                      (jinn $ jleft $ JObject []))))
      `shouldBe`
        (Right (Inn (Right ((), Inn (Right ((), Inn (Left ())))))))
    it "deserialise mu step" $
      (deserialise []
          (TMu [("Nil", T1),
                ("Cons", TProd [(TMu [("Z", T1),
                                      ("S", TVar 0)]), TVar 0])])
        (jinn (jright (jpair
            (jinn (jleft junit))
            (jinn (jright (jpair
                (jinn (jright (jinn (jleft junit))))
                (jinn (jright (jpair
                    (jinn (jright (jinn (jright (jinn (jleft junit))))))
                    (jinn (jleft junit))
                    )))
                )))
            ))))
      `shouldBe`
        (Right (Inn (Right
            ( Inn (Left ())
            , Inn (Right
               ( Inn (Right (Inn (Left ())))
               , Inn (Right
                   ( Inn (Right (Inn (Right (Inn (Left ())))))
                   , Inn (Left ())
                   ))
               ))
            ))))
  describe "specialisation tests" $ do
    it "serialize Specialised list" $
      serialise StandardContext [] (TApp (TName "List" TList) [TNat]) [1,2,3] `shouldBe`
        JArray [JNumber 1, JNumber 2, JNumber 3]

    it "serialises hypergraph definition" $
      serialise StandardContext [] (TApp (TName "" TList)
                                         [TProd [TApp (TName "" TList) [TNat] , TApp (TName "" TList) [TNat]]])
                [([1,2], [0]), ([],[1,2,3])] `shouldBe`
        JArray [ jpair (JArray [JNumber 1, JNumber 2])
                       (JArray [JNumber 0])
               , jpair (JArray [])
                       (JArray [JNumber 1, JNumber 2, JNumber 3])]

  describe "Binary serialisation/deserialisation" $ do

    it "round1 unit" $ shouldBeRoundtrip1 T1 ()

    it "round1 sum" $ shouldBeRoundtrip1 (TSum [T1, T1]) (Right ())

    it "round1 prod" $ shouldBeRoundtrip1 (TProd [T1, T1]) ((), ())

    it "round1 mu base" $ shouldBeRoundtrip1 (TMu [("Nil", T1),
                                                   ("Cons", TProd [(TMu [("Z", T1),
                                                                         ("S", TVar 0)]), TVar 0])])
                                             (Inn (Left ()))

    it "round1 mu step" $ shouldBeRoundtrip1
      (TMu [("Nil", T1),
            ("Cons", TProd [(TMu [("Z", T1),
                                  ("S", TVar 0)]), TVar 0])])
      (Inn (Right ( Inn (Left ())
                  , Inn (Right ( Inn (Right (Inn (Left ())))
                                , Inn (Right ( Inn (Right (Inn (Right (Inn (Left ())))))
                                             , Inn (Left ())
                                             ))
                                ))
                  )))
