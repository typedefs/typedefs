module Test.Typedefs

import Test.Parse
import Test.Haskell

export
testParse : IO ()
testParse = 
  do Parse.testSuite
     Haskell.testSuite