# Vega (2015): class-inclusion audit

Vega's Definition 3.1 concerns a class of pair languages. Theorems 5.3
and 6.2 identify that class with NP and P, respectively, after showing
that an NP-complete pair problem and a P-complete pair problem belong to it.
The disputed inference is from those memberships and closure properties to
**equality** of the classes. It requires both class inclusions under a
specified encoding of pairs as strings and compatible reductions.

The [Lean](lean/VegaRefutation.lean) and [Rocq](rocq/VegaRefutation.v)
files prove a finite countermodel to the bare logical inference: two
different classes can both be included in a common class. They also show
that a non-injective single-string map applied to both coordinates need
not preserve a diagonal pair language. These results expose missing
justification in the proposed transfer; they are not a model of the
paper's particular SAT reduction or its runtime bounds.

The previous formalization claimed that a diagonal P language could not
be represented by Definition 3.1 because certificate-ignoring verifiers
cannot force x=y. The new proofs show that a shared certificate can encode
the equality condition. Thus that blocked proof was not a refutation of
Theorem 6.1. Ignoring certificates does prove that Cartesian products of
P languages are in the toy class, but it does not make every member a
Cartesian product.

**Classification: concrete refutation of the inclusion-to-equality
inference; identified gap in applying it to Vega's full construction.**
The local predicates omit polynomial runtime and certificate-length
bounds. Pair and string languages can be related by an explicit encoding;
the difference between their types alone is not a mathematical
impossibility result. The forward proof files retain assumptions and
incomplete steps and should be read as sketches.
