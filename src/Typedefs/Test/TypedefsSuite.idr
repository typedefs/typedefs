module Typedefs.Test.TypedefsSuite

import Typedefs.Test.DebugTests
import Typedefs.Test.ParseTests
import Typedefs.Test.HaskellTests
import Typedefs.Test.JSONTests
import Typedefs.Test.ReasonMLTests
import Typedefs.Test.TermParseWriteTests
import Typedefs.Test.JSONFormatTests

export
testSuite : IO ()
testSuite =
  do ParseTests.testSuite
     HaskellTests.testSuite
     ReasonMLTests.testSuite
     JSONTests.testSuite
     TermParseWriteTests.testSuite
     DebugTests.testSuite
     JSONFormatTests.testSuite
