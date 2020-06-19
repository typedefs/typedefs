
# Typedefs Syntax

This document explains the brand new Typedefs Syntax for Typedefs.

## Building blocks

This new Typedefs syntax only has a couple of building blocks: `0`, `1`, `+`, `*` and `^`.

- `0` represents the empty type, an irrepresentable type with no inhabitants. Most useful when used
with `+` and type parameters.
- `1` represents the unit type. It has a single inhabitant which is trivially constructible.
- `+` Addition: Allows you to pick a single value between two possible types, much like a disjoint
union.
- `*` Mutliplication: Allows you to package two types together in a single value, effectively
making pairs and tuples.
- `^` Power: Multiple uses of `*`:  `a * a * a = a ^ 3`.

For more details look at the [Theoretical tutorial](TUTORIAL_UNDERSTANDING_TYPEDEFS.md)

You can build Typedefs with those simple building blocks by binding them to a name with `:=` and
ending with `;` :

```
Bool := 1 + 1;

Byte := Bool ^ 8;
```
This example defines a Typedef `Bool` and a Typedef `Byte` which is a product of 8 `Bool`s.

## Type parameters

If the type you want to define takes a type parameter you can define it by following its name by
variable names:

```
Maybe a := 1 + a;

Either a b := a + b;
```

This example defines a Typedef `Maybe` which takes a type parameter `a` and is used as the second
alterntive to `Maybe`. `Either` takes two type parameters and says that a value is either the first
one or the second one.

## Type application

If you want to refer to a type that's already been defined you can simply refer to its name like
we've seen with the `Byte` example. However, you can only use _fully applied types_.

```
BoolOrBit := Either Bool Byte;
```

The example with type parameters can be rewritten this way:

```
Either a b := a + b;

Maybe a = Either 1 a;
```

## Recursive types and named sums

If you want to define types that refer to themselves for a tree-like structure, you will need to
express the type as reference to itself. However this syntax does not work:

```
List a := 1 + (a * List a)
```

Indeed we require self-referential types to name each of their constructors using the following
syntax:

```
List a := Nil : 1 | Cons : (a * List a)
```

Where the `|` operator acts like `+` when dealing with named constructors. This syntax is reminiscent
of ML-like languages, which allow you to define data types with multiple constructors. This is also
the case here:

```
Tree a b := Tensor   : (Tree a b) * (Tree a b)
          | Sequence : (Tree a b) * (Tree a b)
          | Sym      : a * a
          | Id       : a
          | Mor      : b
```

(This example was directly taken from our `FSM-oracle` project.)

## Named fields

You can also use the `|` syntax to include names for your type constructors if you find that `+`
obscures the meaning of your constructors. However, `|`-declarations cannot be nested, whereas
`+`, `*` and `^` can.

```
Bool := True : 1 | False : 1

Either a b := Left : a | Right : a

List a := Nil : 1 | Cons : (a * List a)

Maybe a := None : 1 | Some : a
```

## Future work

### Records

It would be nice if we had a record syntax to go along with `|` syntax:

```
User := { age : Int
        , name : String
        }
```

### Partial application

The following would be nice to have.

```
Either a b := a + b

Maybe a = Either 1
```


## End remarks

If you are familiar with Typedefs, you will notice that `mu`, `app` and `var` are
missing. This is because the new syntax mostly supersedes those constructors and compiles
down to a representation that uses them.

If you still want to write your typedefs in terms of `mu`, and `app` you can still use
the s-expression syntax available with the `--s-exp-syntax` flag
