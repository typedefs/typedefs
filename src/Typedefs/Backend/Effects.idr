module Typedefs.Backend.Effects

import Data.Vect
import Data.SortedMap

import Typedefs.Typedefs
import Typedefs.Names
import Typedefs.Either
import Typedefs.Backend.Data
import Typedefs.Backend.Specialisation

import Effects
import Effect.State
import Effect.Exception

export
traverseEffect : {b : Type} -> {e : List EFFECT}
              -> (a -> SimpleEff.Eff b e) -> Vect k a
              -> SimpleEff.Eff (Vect k b) e
traverseEffect f []        = pure []
traverseEffect f (x :: xs) = do v <- f x
                                vs <- traverseEffect f xs
                                pure $ v :: vs

-- The state containing all the specialised types.
public export
SPECIALIZED : Type -> EFFECT
SPECIALIZED targetType = 'Spec ::: STATE (SortedMap String targetType)

||| Environment, contains currently used variables and names
public export
ENV : (clauseType : Type) -> Nat -> EFFECT
ENV clause n = 'Env ::: STATE (SortedMap String Nat, Vect n clause)

||| Errors that the compiler can throw.
public export
ERR : EFFECT
ERR = EXCEPTION CompilerError

-- The state of already generated definitions
public export
NAMES : EFFECT
NAMES = 'Names ::: STATE (List Name)

-- The context in which specialized type lookup is done
public export
LookupM : Type -> Type -> Type
LookupM targetType t = Eff t [SPECIALIZED targetType, ERR]

export
runLookupM : Specialisation t => LookupM t a -> Either CompilerError a
runLookupM m = runInit ['Spec := specialisedTypes, default] m

-- The context in which definition are generated.
-- Keeps track of generated names and requires specialized types lookup
public export
MakeDefM : Type -> Type -> Type
MakeDefM target t = Eff t [NAMES, SPECIALIZED target, ERR]

toEff : Either CompilerError a -> Eff a [ERR]
toEff (Left err)  = raise err
toEff (Right val) = pure val

export
runMakeDefM : Specialisation t => MakeDefM t a -> Either CompilerError a
runMakeDefM m = runInit ['Names := [], 'Spec := specialisedTypes, default] m

-- idk why this is necessary sometimes
export
subLookup : LookupM target value -> MakeDefM target value
subLookup m = m

||| Monad for the term generator, keeping track of a name supply (in
||| the form of a map of the number of usages for each name) and a
||| "semantic" environment consisting of an environment of types, and
||| terms for decoding/encoding the types.
||| @ n the size of the environment
public export
TermGen : (definition : Type) -> (n : Nat) -> Type -> Type
TermGen def n t = SimpleEff.Eff t [Effects.ENV def n, SPECIALIZED def, ERR]

export
toTermGen : Either CompilerError a -> TermGen d n a
toTermGen (Left err) = raise err
toTermGen (Right val) = pure val

export
runTermGen : Specialisation defs => (env : Vect n defs) -> TermGen defs n a -> Either CompilerError a
runTermGen env mx {defs} = runInit (initialState env) mx
  where -- For some reason, inlining this definition will make type inference confused and infer that as
    -- `Env eff […]` instead of `Env (Either CompilerError) […]`
    initialState : (env : Vect n defs) -> Env (Either CompilerError)
      [ STATE (LRes 'Env (SortedMap String Nat, Vect n defs))
      , STATE (LRes 'Spec (SortedMap String defs))
      , EXCEPTION CompilerError
      ]
    initialState env = ['Env := (empty, env), 'Spec := specialisedTypes, default]

||| Only perform an action if a name is not already present in the state. If the action is performed, the name will be added.
export
ifNotPresent : {t : Type} -> Name -> MakeDefM t (List def) -> MakeDefM t (List def)
ifNotPresent n gen =
  if n `List.elem` !('Names :- get)
    then pure []
    else 'Names :- update (n ::) *> gen

extendContextEff : TDef n -> SortedMap String b -> Vect n b
               -> Eff (k ** (TDefR (n + k), Vect (n + k) b)) [ERR]
extendContextEff td m v = Backend.Effects.toEff $ mapLeft RefNotFound $ extendContext td m v
