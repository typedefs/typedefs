import Data.Fin
import Data.Vect

%default total

Name : Type
Name = String


data TDef : (n:Nat) -> Type where
  T0 : TDef n
  T1 : TDef n
  TSum : TDef n -> TDef n -> TDef n
  TProd : TDef n -> TDef n -> TDef n
  TVar : Fin (S n) -> TDef (S n)
  TMu : Name -> List (Pair Name (TDef (S n))) -> TDef n

mutual
  data Mu : Vect n Type -> TDef (S n) -> Type where
    Inn :  Ty (Mu tvars m :: tvars) m -> Mu tvars m

  Ty : Vect n Type -> TDef n -> Type
  Ty tvars T0 = Void
  Ty tvars T1 = Unit
  Ty tvars (TSum x y) = Either (Ty tvars x) (Ty tvars y)
  Ty tvars (TProd x y) = Pair (Ty tvars x) (Ty tvars y)
  Ty tvars (TVar v) = Vect.index v tvars
  Ty tvars (TMu _ m) = Mu tvars (args m)
    where args [] = T0
          args [(_,m)] = m
          args ((_,m)::ms) = TSum m (args ms)

------ meta ----------

pow : Nat -> TDef n -> TDef n
pow Z _ = T1
pow (S n) a = TProd a (pow n a)


------ examples ------

bit : TDef Z
bit = TSum T1 T1

byte : TDef Z
byte = pow 8 bit

list : TDef 1
list = TMu "list" ([("nil", T1), ("cons", TProd (TVar 1) (TVar 0))])

nil : (A : Type) -> Ty [A] Main.list
nil x = Inn $ Left ()

cons : (A : Type) -> A -> Ty [A] Main.list -> Ty [A] Main.list
cons A x xs = Inn $ Right (x, xs)

maybe : TDef 1
maybe = TSum T1 (TVar 0)

nothing : (A : Type) -> Ty [A] Main.maybe
nothing _ = Left ()

just : (A : Type) -> A -> Ty [A] Main.maybe
just A = Right

test : Type
test = Ty [] bit

------- compile to Idris ? -----

defType : String -> String -> String
defType name def = name ++ " : Type\n" ++ name ++ " = " ++ def

compileClosed : TDef n -> String
compileClosed T0 = "Void"
compileClosed T1 = "Unit"
compileClosed (TSum x y) = "Either (" ++ (compileClosed x) ++ ") (" ++ (compileClosed y) ++ ")"
compileClosed (TProd x y) = "Pair (" ++ (compileClosed x) ++ ") (" ++  (compileClosed y) ++ ")"
compileClosed (TMu _ x) = "mu youare fuxed"
compileClosed (TVar x) = "var you are fcjked"

-------- printing -------

parens : String -> String
parens s = "(" ++ s ++ ")"

curly : String -> String
curly s = "{" ++ s ++ "}"

showOp : String -> String -> String -> String
showOp op x y = parens $ x ++ " " ++ op ++ " " ++ y

mutual
  showTDef : TDef n -> String
  showTDef T0 = "0"
  showTDef T1 = "1"
  showTDef (TSum x y) =  showOp "+" (showTDef x) (showTDef y)
  showTDef (TProd x y) =  showOp "*" (showTDef x) (showTDef y)
  showTDef (TVar x) = curly $ show $ toNat x
  showTDef (TMu n ms) = n ++ " = mu [" ++ (showTDefs ms) ++ "]"

  showTDefs : List (Pair Name (TDef n)) -> String
  showTDefs [] = ""
  showTDefs [(n,x)] = n ++ ": " ++ showTDef x
  showTDefs ((n,x)::xs) = (n ++ ": " ++ showTDef x) ++ ", " ++ showTDefs xs


main : IO ()
main = do
     putStrLn $ showTDef Main.list


{-q
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
-}

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

