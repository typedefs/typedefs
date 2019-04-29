module Test.TypedefsSuite

import Test.ParseTests
import Test.HaskellTests
import Test.JSONTests
import Test.ReasonMLTests
import Test.TermWriteTests
import Test.TermParseTests

export
testSuite : IO ()
testSuite =
  do ParseTests.testSuite
     HaskellTests.testSuite
     ReasonMLTests.testSuite
     JSONTests.testSuite
     TermWriteTests.testSuite
     TermParseTests.testSuite
