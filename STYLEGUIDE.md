
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
  where g : String
        g = "hello"
```

Where clauses are aligned with 6 spaces

### Indentation: Let declarations

```idris
fn : String
fn = let greeting = "hello" in
         greeting
```

Let declarations are indented with 4 spaces

### Indentation: rewrites

```idris
fn : String
fn = rewrite proof in
             1234
```

Rewrite rules are indented with 8 spaces

### Indentation: Case

```idris
fn : String
fn = case True of
          True => "Hello"
          False => "Goodbye"
```

Case analysis is indented with 5 spaces

## Alignment ASCII-art

Sometimes, syntax in idris can become very verbose in places where 
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

