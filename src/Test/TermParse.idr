module Test.TermParse

import Data.Vect

import Typedefs
import Names
import TermParse
import TParsec

import Specdris.Spec

%access public export

testSuite : IO ()
testSuite = spec $ 

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
