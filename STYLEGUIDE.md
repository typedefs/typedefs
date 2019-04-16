
# Typedefs styleguide

This styleguide aims to answer questions relevants to the cosmetics related to
writing Idris programs.

Since idris is a relatively young language, there is no general convention
about its style. This document should serve as reference for current and future
users of the typedefs codebase.

## Line length: 120

The maximum line length is 120 characters. In today's wide screen monitors
there is no reason to limit ourselves to 80 characters, yet, having a maximum
limit helps avoiding degenerate situations.

## Indent style: 2 spaces

Idris makes uses of some whitespace sensitive construction (typically the `do`
notation), and also inherits from a culture of ascii-art code from Agda and
Haskell. In order to allow this level of visual customisation and ensure
consistency across editors, spaces are used.

The language does not benefit from more than 2 space of indentation in most
cases. Thought special constructions lend themselve to more spaces for
indentation.

### Indentation: where clauses

``` idris
fn : String
fn = g
  where
    g : String
    g = "hello"
```

Where clauses are aligned with 2 spaces

### Indentation: Let declarations

```idris
fn : String
fn = let greeting = "hello" in
       greeting
```

Let declarations are indented with 2 spaces.

Additional declarations are indented with 4 spaces while the expression is lined up with declarations.

```idris
fn : String
fn = let greeting = "hello"
         whom = "world"
      in greeting
```

### Indentation: rewrites

```idris
fn : String
fn = rewrite proof in
       1234
```

Rewrite rules are indented with 2 spaces. Multiple rewrite rules in a row are not indented.

```idris
fn : String
fn = rewrite proof in
     rewrite proof2 in
       1234
```

This because, even though they syntactically look like `let` declarations, unlike them, it is not
allowed to bundle multiple rewrites in the same block.

### Indentation: Case

```idris
fn : String
fn = case True of
       True => "Hello"
       False => "Goodbye"
```

Case analysis is indented with 2 spaces

## Type signatures

Idris can be quite verbose when declaring type signature, indeed type signatures can carry:

- Interface constraints
- Programs and function calls
- Named parameters
- All of the above


### Type signatures: Argument grouping

In the case where multiple named arguments with the same type appear in a row, they should be
grouped in a single declaration. This helps comunicate the fact that all those arguments
share the same type and are only different in name.

```idris
fn : (a, b, c : Type) -> Type
fn = …
```

### Type signatures: many arguments

In case a type signature is too long to fit in the 120-character limit, or if breaking it up would
significantly improve its readability, it is expected to follow the following pattern.

```idris
veryLongTypeSignature :
     firstArgument : Type
  -> secondArgument : Type
  -> (ThisFunctionIsVerylongArgument -> secondArgument)
  -> Type
```

This allows the  reader to scan the signature vertically in order to read the entirety of the type signature.


### Type signatures: many interfaces

In case a type signature is too long to fit in the 120-character limit because of interfaces
definitions, it is expected to break it up as follows:

```idris
veryLongFunctionBecauseOfInterfaces :
   ( Interface1 a
   , Interface2 b
   , Interface3 c )
  => (a, b, c : Type)
  -> Type
```

Again this allows the reader to scan the function verticaly and get all the information regarding
interfaces. The extra leading whitespaces help to indicate that those are interface constraints
and not arguments.

### Type signatures: dependent signatures


In cases where a dependent type denotes some sort of computation, that computation is expected to
be written in an auxiliary function rather than inside the type signature.

```idris
Select : Bool -> Type
Select True = String
Select False = Int

dependent : (a : Bool) -> Select a
dependent True = ""
dependent False = 0
```

## Alignment ASCII-art

Sometimes, idris syntax can be very verbose in places where
understanding the structure of the program is key.

```
postulate hardToRead : (N (N a b) c) = (N a (N b c))
```

In this case it might be relevant to align the code as follows

```
easierToRead: (N (N a b) (  c  )) =
              (N (  a  ) (N b c))
```

As we can see, the _structure_ of the equality is much easier to see (a form of
associativity here). Since this is ascii art, there are multiple equally
valid ways of aligning this expression. Here are some examples:

1.

```
easierToRead: (N (N a b) c      ) =
              (N a       (N b c))
```
2.
```
easierToRead: (N (N a b)       c) =
              (N       a (N b c))
```
3.
```
easierToRead: (N (N a    b) c) =
              (N    a (N b  c))
```

Using operators, one could write:

4.
```
infixl 5 @@

(@@) : Type -> Type -> Type
(@@) = N

postulate easierToRead : a @@ (b @@ c) = (a @@ b) @@ c
```

There is no strictly better solution, (ascii-)art is a matter of taste. But we
can elaborate the following rule: If during review your ascii art does not make
it clear to every reviewer what its intent is, remove it.

If a user come up with solution (3.) and reviewers are unhappy, the code should
be changed to

```
backToHardToRead : (N (N a b) c) = (N a (N b c))
```

This is to avoid spending review time on aesthetics rather than functionality.

If aethetics disagreement persists, an issue should be opened to address it.

### Alignment: Vertical symbols

It is generally encouraged to vertically align symbols in declarations of functions, `case`-blocks,
and `with`-blocks.

```idris
case bool of
  True  = …
  False = …
```

```idris
fn : Type -> Type
fn a with (view a)
  fn (S x) | view = …
  fn Z     | view = …
```

```idris
boolFunc : Bool -> Bool
boolFunc False = …
boolFunc True  = …
```
