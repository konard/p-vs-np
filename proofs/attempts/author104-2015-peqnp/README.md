# Frank Vega (2015): P=NP attempt via equivalent-P

**Attempt ID:** 104 · **Source:** [HAL hal-01161668](https://hal.science/hal-01161668),
“Solution of P versus NP Problem”

Vega defines equivalent-P (∼P) for languages of pairs whose components
have P verifiers sharing a certificate. Theorem 5.2 proposes an e-reduction
from a diagonal one-in-three 3SAT problem to a pair problem in ∼P.
Theorem 6.1 claims a diagonal HORNSAT pair language belongs to ∼P.
Theorems 5.3 and 6.2 then infer ∼P=NP and ∼P=P and conclude P=NP.

## Audited result

The [refutation notes](refutation/README.md) identify the missing
class-inclusion direction in those equality inferences. The
[Lean](refutation/lean/VegaRefutation.lean) and
[Rocq](refutation/rocq/VegaRefutation.v) files give a finite logical
countermodel to inferring equality from membership and closure alone.
They also test a diagonal reduction and show how a shared certificate
can represent the diagonal of a P language in the toy definition.

**Evidence level: identified gap with a concrete logical countermodel.**
The model does not formalize polynomial time, the paper's specific SAT
instances, or a complete characterization of ∼P. Pair languages can be
encoded as string languages, so merely calling the expressions different
types does not refute a possible encoded equality. The issue is that the
needed encoding, compatible reductions, and reverse inclusions are not
established by the cited steps.

The [forward files](proof/README.md) are sketches with assumptions and
unfinished obligations. The original text is archived as
[Markdown](ORIGINAL.md) and [PDF](ORIGINAL.pdf).
