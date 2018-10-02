import Typedefs
import Parse

main : IO ()
main = do
  [_, str] <- getArgs
  putStrLn $ parseThenShowTDef str
