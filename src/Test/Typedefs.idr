module Test.Typedefs

import Test.Parse
import Test.Haskell
import Test.ReasonML
import Test.TermWrite
import Test.TermParse

export
testSuite : IO ()
testSuite =
  do Parse.testSuite
     Haskell.testSuite
     ReasonML.testSuite
     TermWrite.testSuite
     TermParse.testSuite