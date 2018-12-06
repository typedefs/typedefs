module Backend.Utils

import Data.Vect

%default total
%access public export

-- TODO exists after 1.3 in Control.Isomorphism.Vect            
unindex : (Fin n -> a) -> Vect n a
unindex {n=Z}   _ = []
unindex {n=S k} f = f FZ :: unindex (f . FS)

withSep : String -> (a -> String) -> Vect k a -> String
withSep sep fn xs = concat $ intersperse sep $ map fn xs
