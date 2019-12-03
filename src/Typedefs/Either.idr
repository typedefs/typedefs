module Typedefs.Either

export
bimap : (a -> k) -> (b -> l) -> Either a b -> Either k l
bimap f _ (Left l) = Left (f l)
bimap _ f (Right r) = Right (f r)

export
mapLeft : (a -> b) -> Either a k -> Either b k
mapLeft f (Left v)  = Left (f v)
mapLeft f (Right v) = Right v