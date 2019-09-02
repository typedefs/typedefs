module Typedefs.Test.TermParseWriteTests

import Typedefs.Typedefs
import Typedefs.Names
import Typedefs.TermParse
import Typedefs.TermWrite

import Data.Vect
import Data.Bytes
import Data.ByteArray
import TParsec
import Specdris.Spec

%access public export

roundtrip1 : (td : TDefR 0) -> Ty [] td -> Maybe ((Ty [] td), Bytes)
roundtrip1 td x = deserializeBinaryClosed td $ serializeBinaryClosed td x

roundtrip2 : (td : TDefR 0) -> Bytes -> Maybe Bytes
roundtrip2 td b = map (serializeBinaryClosed td . fst) (deserializeBinaryClosed td b)


testSuite : IO ()
testSuite = spec $ do

  describe "TermWrite" $ do

    it "serialize unit" $
      (serialize [] [] T1 ()) `shouldBe` "()"

    it "serialize sum" $
      (serialize [] [] (TSum [T1, T1]) (Left ())) `shouldBe` "(left ())"

    it "serialize prod with var" $
      (serialize [Integer] [show] (TProd [T1, TVar 0]) ((), 2)) `shouldBe` "(both () 2)"

    it "serialize mu" $
      (serialize [Integer] [show] (TMu [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]) (Inn $ Right (1, Inn $ Right (2, Inn $ Left ()))))
      `shouldBe`
      "(inn (right (both 1 (inn (right (both 2 (inn (left ()))))))))"

  describe "TermParse" $ do

    it "deserialize unit" $
      (deserialize [] [] T1 "()") `shouldBe` (Just ())

    it "deserialize sum" $
      (deserialize [] [] (TSum [T1, T1]) "(left ())") `shouldBe` (Just (Left ()))

    it "deserialize prod with var" $
      (deserialize [Integer] [decimalInteger] (TProd [T1, TVar 0]) "(both () 2)") `shouldBe` (Just ((), 2))

--    it "deserialize mu" $
--      (deserialize [Integer] [decimalInteger] (TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]) "(inn (right (both 1 (inn (right (both 2 (inn (left ()))))))))")
--      `shouldBe`
--      (Just (Inn (Right (1, Inn (Right (2, Inn (Left ())))))))
{-
  describe "Binary serialisation/deserialisation" $ do

    it "round1 unit" $ roundtrip1 T1 () `shouldBe` (Just ((), empty))

    it "round1 sum" $ roundtrip1 (TSum [T1, T1]) (Right ())  `shouldBe` (Just ((Right ()), empty))

    it "round1 prod" $ roundtrip1 (TProd [T1, T1]) ((), ())  `shouldBe` (Just (((), ()), empty))

    it "round1 mu base" $ roundtrip1 (TMu [("Nil", T1), ("Cons", TProd [(TMu [("Z", T1), ("S", TVar 0)]), TVar 0])]) (Inn (Left ()))
      `shouldBe` (Just ((Inn (Left ())), empty))

    it "round1 mu step" $ roundtrip1 (TMu [("Nil", T1), ("Cons", TProd [(TMu [("Z", T1), ("S", TVar 0)]), TVar 0])]) (Inn (Right ((Inn (Left ()), Inn (Right ((Inn (Right (Inn (Left ()))), Inn (Right ((Inn (Right (Inn (Right (Inn (Left ()))))), Inn (Left ())))))))))))
      `shouldBe` (Just ((Inn (Right ((Inn (Left ()), Inn (Right ((Inn (Right (Inn (Left ()))), Inn (Right ((Inn (Right (Inn (Right (Inn (Left ()))))), Inn (Left ()))))))))))), empty))
-}
