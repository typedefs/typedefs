module Test.TermWriteTests

import Data.Vect

import Typedefs
import Names
import TermWrite

import Specdris.Spec

%access public export

testSuite : IO ()
testSuite = spec $ 

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



