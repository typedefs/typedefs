module Test.Typedefs

import Test.Parse
import Test.Haskell
import Test.TermCodec

export
testSuite : IO ()
testSuite =
  do Parse.testSuite
     Haskell.testSuite
     TermCodec.testSuite
