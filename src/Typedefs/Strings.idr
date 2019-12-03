module Typedefs.Strings

%default total
%access export

parens : String -> String
parens "" = ""
parens s = "(" ++ s ++ ")"

parens' : String -> String
parens' s = if " " `isInfixOf` s then "(" ++ s ++ ")" else s

curly : String -> String
curly "" = ""
curly s = "{" ++ s ++ "}"

square : String -> String
square "" = ""
square s = "[" ++ s ++ "]"