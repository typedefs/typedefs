module Test.Parse

import Parse

%access public
export
  testSuite : IO ()
  testSuite = do
    putStrLn "-- well-formed terms -----------------------------------------------------------"
    putStrLn ""
    Parse.test "Unit"
    Parse.test "(mu list Unit)"
    Parse.test "(mu list (* Unit Unit))"
    Parse.test "(* Unit Unit)"
    Parse.test "(+ Unit Void)"
    Parse.test "(+ Unit (* Unit Void))"

    putStrLn "-- ill-formed terms ------------------------------------------------------------"
    putStrLn ""
    Parse.test "(+ Unit * Unit Void)"
    Parse.test "(+ Unit Unit Void)"
