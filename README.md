example, `idris typedefs.idr`:

	*typedefs> showTDef list
	"list = mu [nil: 1, cons: ({1} * {0})]" : String
	*typedefs> showTDef maybe
	"(1 + {0})" : String


# Quick introduction

We have the `TDef` data-type family that represents a "Type Definition".
It is indexed by a `n:Nat` argument, the number of type variables.

Its constructors are:

- `T0`, the *empty* type
- `T1`, the *unit* type
- `TSum`, the *coproduct* type
- `TProd`, the *product* type
- `TMu`, the *μ* type
- `TVar`, a type variable, referencing using *De Bruijn* indices.

To interpret a type definition as an *Idris* type, there is a `Ty` function,
which you can think of as having this type
```idris
Ty : (α₁ ... αⱼ) → (TDef j) → Type 
```
The function `Ty` takes a vector of `Type`s of length `j`, and a type
definition with `j` holes. It returns an idris `Type`.

For example, define `bit` to be a zero-argument type definition `1 + 1`.
```idris
    bit : TDef Z
    bit = TSum T1 T1
```
Then to interpret this type as an Idris `Type`, run
```idris

    Ty [] bit
    Either () () : Type
```
To define a parametric recursive type, such as list,
```idris
list : (a : type) -> mu (nil : 1 + cons : (a * list a))
```
in code, try this
```idris
    list : TDef 1
    list = TMu "list" (
         [ ("nil", T1)
         , ("cons", TProd (TVar 1) (TVar 0)
         ]
    )
```
Then to interpret it, try
```idris

    Ty [(Ty [] bit)] list
    Mu [Either () ()]
       (TSum T1 (TProd (TVar 1) (TVar 0)) : Type
```

# More information

See [Examples.idr](src/Examples.idr). There is also a [work-in-progress document](https://hackmd.io/22MJzoZFRBycNiDgN1nKKg)
describing the work in progress, and [Jelle's musings on Typedefs and regular languages](hackmd.io/4htwL7Z6QlCyimKc98exJA).
