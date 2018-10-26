module Test.TermCodec

import Data.Vect
import Data.Vect.Quantifiers

import Typedefs
import Types
import TermCodec

import Specdris.Spec

%access public export

testSuite : IO ()
testSuite = spec $ do

  describe "TermParse" $ do
    it "serialize unit" $ (deserialize [] [] T1 "()") `shouldBe` (Just ())

-- serialize [] [] (TSum [T1, T1]) (Left ())
-- "(left ())"

-- deserialize {ts=[]} (TSum [T1, T1]) "(left ())"
-- Just (Left ())

-- serialize [Integer] [show] (TProd [T1, TVar 0]) ((), 2)
-- "(both () 2)"

-- deserialize {ts=[MkDPair Integer decimalInteger]} (TProd [T1, TVar 0]) "(both () 2)"
-- Just ((), 2)

-- serialize [Integer] [show] (TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]) (Inn $ Right (1, Inn $ Right (2, Inn $ Left ())))
-- "(inn (right (both 1 (inn (right (both 2 (inn (left ()))))))))" 

-- deserialize [Integer] [decimalInteger] (TMu "List" [("Nil", T1), ("Cons", TProd [TVar 1, TVar 0])]) "(inn (right (both 1 (inn (right (both 2 (inn (left ()))))))))"
-- Just (Inn (Right (1, Inn (Right (2, Inn (Left ())))))) : Maybe (Mu [Integer] (TSum [T1, TProd [TVar (FS FZ), TVar FZ]]))
