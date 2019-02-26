import Data.Vect
--import Data.Vect.Quantifiers
import TParsec

import Typedefs
import Parse
import TermParse
import Backend
import Backend.Utils
import Backend.Haskell

getSource : JS_IO String
getSource = foreign FFI_JS "getSource()" _

setResult : String -> JS_IO ()
setResult = foreign FFI_JS "setResult(%0)" _

deserialize0 : String -> String -> Maybe (td : TDef 0 ** Ty [] td)
deserialize0 tdstr tmstr = 
  do (n**td) <- parseTDef tdstr   
     case n of 
       Z => (\tm => (td ** tm)) <$> deserialize [] [] td tmstr
       _ => Nothing

main : JS_IO ()
--main = setResult $ parseThenStrFun !getSource (\td => print . generate Haskell $ DPair.snd td)
main = let m1 = deserialize0 "1" "1" in
       case m1 of 
         Just _ => setResult $ parseThenStrFun !getSource (\td => print . generate Haskell $ DPair.snd td)
         Nothing => setResult "foo"