module Parser

import Typedefs
import Parse
import Backend
import Backend.Utils
import Backend.Haskell

main : IO ()
main = do
  [_, str] <- getArgs
  let tpe = parseTNamedEither str
  putStrLn $ "parsed typedef: "
  putStrLn $ either id (\tp => show $ DPair.snd tp) tpe
  putStrLn $ ""
  putStrLn $ "haskell type: " ++ either id (\tp => print . generateDefs Haskell $ DPair.snd tp) tpe
