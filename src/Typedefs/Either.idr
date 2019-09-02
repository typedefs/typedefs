module Typedefs.Either


export
bimap : (a -> k) -> (b -> l) -> Either a b -> Either k l
bimap f _ (Left l) = Left (f l)
bimap _ f (Right r) = Right (f r)
