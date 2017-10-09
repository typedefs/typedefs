infixr 10 .+.
infixr 10 .*.

data Ty = Ty0 | Ty1 | (.+.) Ty Ty | (.*.) Ty Ty

interpTy : Ty -> Type
interpTy Ty0 = Void
interpTy Ty1 = Unit
interpTy (a .+. b) = Either (interpTy a) (interpTy b)
interpTy (a .*. b) = Pair (interpTy a) (interpTy b)

bit : Ty
bit = Ty1 .+. Ty1

pow : Nat -> Ty -> Ty
pow Z _ = Ty1
pow (S z) a = a .*. (pow z a)

nibble : Ty
nibble = pow 4 bit

byte : Ty
byte = pow 8 bit

-- (pow 2 nibble) =iso= byte ???
-- find normal form in O(n) max?

showTy : Ty -> String
showTy x =
  case x of
    Ty0 => "0"
    Ty1 => "1"
    (a .+. b) => showOp "+" a b
    (a .*. b) => showOp "*" a b
  where
    parens : String -> String
    parens s = "(" ++ s ++ ")"
    showOp : String -> Ty -> Ty -> String
    showOp op x y = parens $ (showTy x) ++ " " ++ op ++ " " ++ (showTy y)


-- interpreteren van type definities
--   tau : Ty -> Type
-- codec voor type definities
--   serialise : Ty -> Bits
--   deserialise : Bits -> Ty
-- codec voor termen van type
--   serialise : (t:Ty) -> x:(tau t) -> Bits
--   deserialise : Bits -> (t:Ty ** tau t)

-- prf (a .+. (b .+. c)) == ((a .+. b) .+. c)

-- prf Ty codec :
--   forall t:Ty. (serialise . deserialise) t == t

-- prf Term codec :
--   forall t:Ty. forall (x:tau t). (deserialise . serialise) t x == t

