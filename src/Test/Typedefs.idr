module Test.Typedefs

import Test.Parse
import Test.Haskell
import Test.JSON
import Test.ReasonML
import Test.TermWrite
import Test.TermParse

export
testSuite : IO ()
testSuite =
  do Parse.testSuite
     Haskell.testSuite
     ReasonML.testSuite
     JSON.testSuite
     TermWrite.testSuite
     TermParse.testSuite