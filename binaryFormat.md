
# Typedefs binary format

Terms are serialised in a type-directed way, given a typedefs
description --- terms make no sense on their own. If the type is
unknown, a description of the type could first be serialised, followed
by the serialisation of the term (this is future work).

Terms are serialised as follows:

- Terms of type `T0` or `T1` do not need to be serialised --- the former does not exist, and the latter are trivial.
- Terms of type `TSum ts` with `|ts| = 2 + k` are serialised as an integer `i` (with `i < 2 + k`, but this is not exploited), followed by the serialisation of a term of type `ts[i]`.
- Terms of type `TProd ts` with `|ts| = 2 + k` are serialised as the serialisation of `ts[0]`, ..., `ts[1+k]`. This relies on being able to compute the width of each serialised term.
- Terms of type `Tvar j` are serialised with a given "parameter" serialiser --- this is used to serialise `TMu`s.
- Terms of type `Tmu ts` with |ts| = k are serialised as an integer `i` (with `i < k`, but this is not exploited), followed by the serialisation of a term of type ts[i], where the "parameter" serialiser for the new type variable is instantiated to this described procedure.
- Terms of type `TApp f xs` with `|xs| = k` are serialised as terms of type `f`, with "parameter" serialisers given by the `k` serialisations of terms of type `xs[k]`.
