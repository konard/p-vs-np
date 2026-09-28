# Groff (2011): finite-field evaluation audit

The disputed inference is that evaluating a polynomial whose coefficients
encode satisfying assignments at one field point determines whether its
satisfying-assignment count is zero. The previous Lean and Rocq statements
used arbitrary functions or an abstract pigeonhole argument and did not
construct a pair of k-SAT formulas with the same evaluation.

The [Lean](lean/GroffRefutation.lean) and [Rocq](rocq/GroffRefutation.v)
files now use two actual three-variable, eight-clause 3-CNF formulas. Each
full three-literal clause is indexed by its unique falsifying assignment.
One formula has satisfying assignments 0, 3, and 5; the other has none.
At x=3 modulo 271, both raw truth-table polynomials evaluate to zero.
The modulus is prime by trial division through 16 and exceeds (2n)²=256,
matching the paper's stated size condition for n=8.

**Classification: conditional result.** This proves that one *raw*
polynomial evaluation cannot determine SAT on these inputs. Groff also
changes coefficients, performs further operations and evaluations, and
solves a linear system. Those later steps are not modeled here, so this
collision is not a counterexample to the complete algorithm. An explicit
2^V-coefficient representation has exponential length, but that fact
alone gives no lower bound for a symbolic or circuit representation.
The paper's stated nonzero error probability also does not give a
deterministic polynomial-time algorithm without an additional argument.

The [forward sketches](../proof/README.md) are separate and retain
unproved obligations.
