
# Tutorial: Understanding Typedefs

This tutorial is aimed at developpers unfamiliar the concepts that drive Typedefs and
attempts to teach them from the bottom up.
It is not strictly necessary in order to start using Typedefs but is very useful in
order to learn how to understand how to achieve certain goals intuitively.
If you are familiar with functional programming or curious about how Typedefs works, this tutorial
is for you. Beyond that, it assumes very little knowledge from the reader.

## Algebras

Typedefs is commonly called, in the mathematics jargon, an Algebra. More
specifically an F-Algebra. Algebras allow us to describe objects with some structure
using pre-defined _terms_. In our case the terms represent our types and the operation
represent the shape of the type. Before we dive into types as an algebra
let us first define and understand what an algebra is in the general sense.

## Terms and operations

You might be familiar with algebra in high school where you are taught to solve equations
like:

```
3x + 5 = 17
```

Where solving means "reduce the equation such that we end up with an expression of the
shape `x = _`". In high school, `x` meant "here is a number, we don't know anything about
it but we know there is one" and `=` meant "what is on the left is equal to what is
on the right".

You might notice that we've used quite a lot of words without defining them, let's take
a minute to make sure we're on the same page:


#### Term

A term is a textual symbol that represents a value or an object in a mathematical context.

Terms can be combined together using other terms or symbols, combined terms are sometimes
referred to as _expressions_.

Example 1: `3` is a term

Example 2: `3 + 4` is two terms combined with the symbol `+`. Note that we haven't said
what `+` means yet, we will see this in the _evaluation_ step. We might also refer to this
as an _expression_.

Example 3: `3 + 5 = 2` is an equation involving the terms `2` and `3 + 5`. Note that evaluating
this expression with natural numbers will lead to a contradiction.


#### Equation

An equation is a _term_ which has the `=` symbol relating two other terms on each side
of it. Typically it means that the two terms on each side are _equal_ or they _evaluate_
to the same _value_.

Example 1:  `3 = 3` says that `3` is equal to itself.

Example 2: `1 = x` says that x is equal to the term `1`

Example 3: `1 + 3 = x` says that x is equal to `1 + 3` which, after evaluation, is `4`

#### Evaluation

Evaluating an expression allows us to convert terms into other terms. Evaluation rules depend
on the context in which we are working. Usually, evaluation will give some kind of _meaning_
to our terms, and this meaning given to expressions is referred to as the _semantics_ of the
language.

Example 1: `3 + 1` evaluates to `4` when we are using natural numbers

Example 2: `x + 0` evaluates to `x` thanks to the fact that `0` is the identity for addition. Note
that this evaluation doesn't say anything about `x`.

Example 3: `x + 0 = 1` evalutates to `x = 1` which tells us that `x` multiplicative identity.

In those examples we're using our intuition that terms represent numbers. But it turns out they can
represent many different things. For example in

```
x + 1 = 0
```

`1` could be the identity matrix and `0` could be the zero matrix. Which means `x` is the matrix
with only `-1` on the diagonal:

```
     ⎛-1  0  0  0  0⎞
     ⎜ 0 -1  0  0  0⎟
 x = ⎜ 0  0 -1  0  0⎟
     ⎜ 0  0  0 -1  0⎟
     ⎝ 0  0  0  0 -1⎠
```

 _note: this example use 5 dimensions for the matrix but it could be of arbitrary size_
## Typedefs as an algebra

With those definitions clarified we can finally come to "what is an algebra?". An algebra is
a mathematical object that features _symbols_ and _relations between those symbols_. Notice that
this definition says nothing about numbers, equations and evaluation.

This is why in Typedefs, every symbol relates to a type, and the relations between them are
combinations of types. This allow us to write something like `maybe(x) = 1 + x` and make sense
of it as an expression that defines a type. Moreover we will see other surprising properties
such as why `x + x = 2 * x` is not really an equality in typedefs.


## Sets and cardinality as an intuition

In order to understand how types can be valid elements of an algebra we are going to ask _"how
many elements inhabit this type?"_ and use this information to link it back to our algebra. We
are going to use the syntax `size(x) = n` to indicate that the type `x` has `n` elements.

#### Boolean

The boolean type is ubiquitous in programming. It encapsulates the _binary_ nature of computers by
taking one of two values, either `false` or `true`. This is typically encoded in
low level machine code by `0` and `1`, or if you look at electronic circuits, it is encoded by
the _presence of a current_ or the _absence_ of it.

**So how many elements does boolean have?** since there are so few we can enumerate them:

- `False`
- `True`

That's 2.

As a matter of fact we can even implement them as an enumeration:

```Swift
enum Bool {
    case true
    case false
}
```

How is this useful for our algebra? Well maybe we can try to decompose this type into
different algebraic formulas, there is `2 + 0`, `1 + 1`, `0 + 2`, `3 - 1`, `2 * 1` and more…
For our purposes we are going to keep this equation in mind: `size(Bool) = 2 = 1 + 1`

#### 32bits integers

Integers are also extremely common in programming, they are usually encoded as strings of bits of
varying lengths. For this example we are going to look in to 32-bits encoded integers,
since they have a finite number of bits they can draw from, there is a finite amount of
integers. Using 32 bits we can represent all numbers from `0` up to `2^32 - 1` (which is
`4'294'967'295`), adding `1` to this number will either return `0` or throw a runtime error.

**So, how many elements does 32-bits integers have?**

- we start at `0`
- then we have `1`
- then we have `2`
- …
- and finally we have `4'294'967'295`

so that's `size(Int) = 4'294'967'296` elements in total. That's quite a bit more than our `boolean`
type!

#### Pairs of Int and Bool

Unlike Int and Bool, pairs aren't necessarily _common_ in popular programming languages. Most
of them have some sort of encoding for them. Java and C++ a `Pair` class, but do not support
destructuring the pair into its components. `Go` does not have pairs at all except for return
values. And the best `C` can do is rely on structs with void pointers.

Despite this lack of first-class support for pair in popular programming languages, pairs are
extremely useful to _bundle_ related data together. For example we can encode _negative_ 32-bit
integers by combining our previous two
types with a pair

```
(False, 34) // 34 is positive
(True, 34) // 34 is negative
```

**So how many elements does a pair of a boolean and a 32-bits integer have?**

For this one we could again enumerate all possiblities but there is a clever way to go about
it:

- Integers have `2^32 = 4'294'967'296` values.
- Numbers are either positive or negative
- We therefore have `4'294'967'296` positive numbers and `4'294'967'296` negative numbers

So using simple arithmetic we have that our negative numebrs has
`4'294'967'296 + 4'294'967'296 = 2 * 4'294'967'296 = 8'589'934'592` elements.

_Note that we have two representation for `0` we have `(False, 0)` and `(True, 0)`, those are
distinct values even if we give them the same meaning._

The one thing I want to draw attention to is this equation here `2 * 4'294'967'296 = 8'589'934'592`.
Just like we said `1 + 1 = 2` for boolean, let's keep this equation in mind
`size(neg) = size((Bool, Int)) = size(Bool) * size(Int) = 2 * 4'294'967'296 = 8'589'934'592`

#### Optional values

A very useful pattern in modern programming language is the use of an optional type (sometimes
called `Maybe`) that indicate that a value might be missing. Just like pairs, a lot of programming
languages do not feature a "true" optional type (since they require
[Algebraic Data Types](https://en.wikipedia.org/wiki/Algebraic_data_type)) but they still have
_some_ sort of encoding. Typically, Java features an
[`Optional`](https://docs.oracle.com/javase/8/docs/api/java/util/Optional.html) type aimed at
avoiding null pointer exceptions, however, since `Optional` is a reference, it can itself be null.

Let's use the `Swift` definition of optional since it's close to a C-like syntax and captures all
the necessary information we need to understand the `Optional` type.

```Swift
enum Optional<T> {
    case none
    case some(T)
}
```

Which means that an `Optional` type can be one of two values, either `none`, or `some(T)`. The `T`
in the second one refers to a type parameter, which means that a type fits there. We don't know
which one yet, but any type could work. For example `some(3)` is a valid value with `T = Int`,
likewise `some(True)` is also a valid value with `T = Bool`.

**So how many elements does Optional have?**

This one is tricky because there are two answers. Looking at the definition we can reasonably come
to the conclusion that there is only two values in the `enum` and therefore only two values for the
`Optional` type: `some` and `none`.

Another answer is that it depends on the parameter type. Indeed we already mentioned that `some(3)`
and `some(True)` are valid values. If we were to enumerate other values we would have:

- `1` value for `none`
- since `some(True)` is a value, then `some(False)` also is one
- since `some(3)` is a value, so are `some(0)`, `some(1)`, and so on

For the first case, the type parameter could by anything, the only valid value for `none` is `none`.

For the second case, if the type parameter is `Bool` then we have two values for `some`,
`some(True)` and `some(False)`. That's the same amount of values that `Bool` has (2), if we add the
`none` value that's `2 + 1 = 3` values in total

For the last case, if the type parameter is `Int` then we have as many value for the `some` case as
there are `Integer` values. So that's `2^32 = 8'589'934'592`, adding the `none` value that's
`8'589'934'592 + 1 = 8'589'934'593` values.

As we see, the pattern is that the number of elements of `Optional` is the number of element of the
parameter type plus one. So if we use `T` as the type parameter in our `size` syntax
we have `size(optional<T>) = size(T) + 1`

#### Either/Result values

Finally we are going to look at a type that represents two possible alternatives when computing
a value. In Haskell and Scala this is the `Either` type, in Rust and Swift it
is called `Result`. For example the type `Either<String, Int>` has value that can either be `String`
or `Int` but we do not know which on it is. The construction of such a type is very similar to
`Maybe`:

```Swift
enum Either<L, R> {
    case left(L)
    case right(R)
}
```

as we can see the main difference with `Optional` is that we take two type parameters and our `none`
case is now a `left(L)` which hosts a value of type `L`.

**So how many elements does Either have?**

For this case we are going to use what we learned from the `Optional` type and make a guess.

The size of `Optional` was defined as `size(Optional<T>) = size(T) + 1`, but since we have two type
parameters it must make sense that they are both used in the expression.

As it turns out, all our previous definitions using `enum` have the form `size(T) = A + B`. So it
makes sense that, since `Either` is defined as an `enum` it must be something like that

`size(Either<L, R>) = ? + ?`

Since both `L` and `R` must be used it makes sense to assume that it's
`size(Either<L,R>) = size(L) + size(R)`

#### Putting it together

We've seen that pairing up a boolean with `Int` allows to represent negative numbers. But it also
double the number of possible values. If represent this as an equation we have that
`size(Neg) = size(Bool) * size(Int)`

Similarly, the size of types like `Either` or `Optional` is measure with an addition:
`size(Optional<V>) = 1 + size(V)`

As you can see, the operations `+` and `*` follow a pattern: when we are given the _choice_
between values, we use `+`, and when we are given multiple things together, we use `*`.

That is why in Typedefs we call the operation that allows to package multiple types together
`TProd` (for **T**ypedefs **Prod**uct) and the operation that picks a type from a list of
candidates `TSum` (for **T**ypedefs **Sum**).
