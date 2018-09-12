module Test.Typedefs

import Test.TParse

export
testTParse : IO ()
testTParse = do
  Test.TParse.testSuite

export
testParse : IO ()
testParse = do
  Test.Parse.testTokens
  Test.Parse.testSuite
