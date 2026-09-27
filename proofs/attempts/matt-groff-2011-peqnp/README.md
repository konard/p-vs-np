# Matt Groff (2011): P=NP attempt

**Source:** [arXiv:1106.0683v2](https://arxiv.org/abs/1106.0683v2),
“Towards P = NP via k-SAT: A k-SAT Algorithm Using Linear Algebra on Finite Fields”

Groff encodes truth assignments as coefficients of univariate polynomials,
modifies the coefficients, evaluates over a finite field, and uses a linear
system to estimate the number of satisfying assignments. The paper gives a
nonzero false-negative error estimate and presents the method as evidence
for a polynomial-time k-SAT algorithm.

## Audited result

The [refutation notes](refutation/README.md) give an explicit collision of
two 3-CNF formulas at one evaluation of their **raw** truth-table
polynomials. This is a concrete illustration of information lost by that
operation. The paper's later coefficient transformations and recovery
procedure are not covered by the witness.

**Evidence level: conditional result.** The number 2^V measures the length
of an explicit coefficient table, but the local formalization does not
establish the size or running time of Groff's symbolic representation.
Likewise, the probability expression in the paper is a stated error estimate,
not a machine-checked probabilistic algorithm or a deterministic decision
procedure. The analysis identifies proof obligations; it does not establish
a lower bound on every algebraic approach to k-SAT.

The [Lean](refutation/lean/GroffRefutation.lean) and
[Rocq](refutation/rocq/GroffRefutation.v) files prove the finite example.
The [forward files](proof/README.md) are sketches. The locally archived
[reconstruction](original/ORIGINAL.md) and [PDF](ORIGINAL.pdf) contain the
paper's construction.
