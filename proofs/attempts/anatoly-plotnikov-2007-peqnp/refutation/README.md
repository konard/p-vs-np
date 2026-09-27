# Audit of Plotnikov's 2007 P = NP Attempt

The [Lean](lean/PlotnikovRefutation.lean) and [Rocq](rocq/PlotnikovRefutation.v) files audit the logical claims made by the earlier refutation. They do not prove that Plotnikov's algorithm fails.

## What the paper claims

Conjecture 1 says that, for a vertex-saturated digraph whose initial independent set is smaller than another independent set, a fictitious arc can be found whose removal has the specified size property. Theorem 5 on page 9 states that **if Conjecture 1 is true**, the proposed algorithm finds a maximum independent set. The paper reports tests on random graphs but gives no proof of Conjecture 1.

The formalizations represent a VS-digraph and its initial set by an abstract `VSInstance`. The `validInstance` predicate restricts the conjecture to instances actually produced by the paper's construction; its definition remains open. `Conjecture1` says that when such an instance has a larger independent set, some fictitious arc leaves an induced set of size at least `|V⁰| − 1`. `AlgorithmCorrect` says the proposed algorithm finds a maximum independent set for every input in the paper's graph class. `correctness_if_conjecture` takes both Conjecture 1 and the Theorem 5 implication as premises. Neither premise is asserted as a fact.

These predicates are still abstract. A full formal verification would need graph definitions, an implementation of the algorithm, a proof that the predicates express its behavior, and proofs of the premises. Compilation of these files establishes only the stated conditional logic.

## Corrections to the earlier refutation

- `P → P` is a valid identity implication. It cannot yield `P` without another premise; `identity_does_not_establish_claim` gives the precise logical statement. The former `circular_reasoning_error` axiom instead negated a theorem and entailed `False`.
- From `Conjecture1 → AlgorithmCorrect`, failure to prove Conjecture 1 does **not** imply `¬AlgorithmCorrect`. The former universal `algorithm_requires_conjecture` axiom also implied `False` for unrelated propositions.
- The old Dilworth axiom asserted that a cubic function was not polynomial. Both files now prove `cubic_is_polynomial`. A minimum chain partition of a finite poset can be computed using polynomial-time matching; the graph-to-poset correspondence and full algorithm still require justification.
- The former complexity axiom inferred failure of an O(n⁸) bound from `¬Conjecture1`. Correctness and running time are distinct. `polynomial_time_if_bound` requires an actual bound on the running-time function.
- The former NP-completeness axiom implied any proposition from arbitrary propositions. The standard consequence of a polynomial exact maximum-independent-set algorithm needs a correctly specified algorithm and reduction; those are outside this abstraction.

## Remaining obligations

1. Define the paper's VS-digraph, fictitious-arc removal, and maximum-independent-set algorithm precisely.
2. Prove Conjecture 1 or find a counterexample.
3. Prove Theorem 5 for the implemented algorithm, using precisely stated assumptions.
4. Prove the claimed O(n⁸) running-time bound, including all iterations and arc tests.

The observed gap means the paper does not establish P = NP. It does not prove P ≠ NP, a counterexample to Conjecture 1, or an impossibility result for the proposed algorithm.

See the [attempt overview](../README.md), [source reconstruction](../ORIGINAL.md), and [forward proof sketch](../proof/README.md).
