# Typedefs

Programming language agnostic type construction language based on polynomials.

See http://typedefs.com/

[![Build Status](https://travis-ci.com/typedefs/typedefs.svg?branch=master)](https://travis-ci.com/typedefs/typedefs)

## Examples

```
$ cd src
$ idris Examples.idr
```

```
*Examples> showTDef list
"list = mu [nil: 1, cons: ({1} * {0})]" : String
*Examples> showTDef maybe
"(1 + {0})" : String
```

## Quick introduction

For some background on algebraic data types, see [The algebra (and calculus!) of algebraic data types](https://codewords.recurse.com/issues/three/algebra-and-calculus-of-algebraic-data-types) by Joel Burget.

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

in code, try
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

## More information

See [Examples.idr](src/Examples.idr). There is also a [work-in-progress document](https://hackmd.io/22MJzoZFRBycNiDgN1nKKg)
describing the work in progress, and [Jelle's musings on Typedefs and regular languages](https://hackmd.io/4htwL7Z6QlCyimKc98exJA).

## Building

Nix package descriptions and a Makefile is provided with build instructions.

### Nix packages

Build everything:

`nix-build`

Build a specific package:

`nix-build -A typedefs.nix`

### Makefile

Build everything:

`make`

Build a specific package:

`make build pkg=typedefs`

Build documentation:

`make doc-all`

Run tests:

`make test-all`

Clean up:

`make clean-all`
