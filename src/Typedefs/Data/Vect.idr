
module Typedefs.Data.Vect

import Data.Vect

public export
append : a -> Vect n a -> Vect (S n) a
append a [] = [a]
append a (x :: xs) = x :: append a xs
