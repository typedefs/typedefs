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

  describe "TermCodec" $ do
    it "serialize something" $ (serialize {ts=[]} (T1) ()) `shouldBe` "(left 1)"
