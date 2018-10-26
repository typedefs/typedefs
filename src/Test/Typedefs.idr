module Test.Typedefs

import Test.Parse
import Test.Haskell
import Test.TermWrite
import Test.TermParse

export
testSuite : IO ()
testSuite =
  do Parse.testSuite
     Haskell.testSuite
     TermWrite.testSuite
     TermParse.testSuite
