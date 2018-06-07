module Test.Typedefs

import Test.Parse

export

testSuite : IO ()
testSuite = do
     Test.Parse.testSuite
