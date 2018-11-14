module Test.Typedefs

import Test.Parse
import Test.Haskell
import Test.ReasonML
import Test.TermCodec

export
testSuite : IO ()
testSuite =
  do Parse.testSuite
     Haskell.testSuite
     ReasonML.testSuite
     TermCodec.testSuite
