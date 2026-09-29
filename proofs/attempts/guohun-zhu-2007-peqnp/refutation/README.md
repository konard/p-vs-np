# Zhu (2007): projector component and matching-count counterexamples

Theorem 1(c3) claims that a projector graph of a Γ digraph with n vertices
has at most n/4 four-cycle components. Lemma 4 separately claims an upper
bound of n/2 **unlabeled** perfect matchings. The paper counts labeled
matchings as exponential; the inequality 2^k > 2k alone does not challenge
the unlabeled claim.

[ZhuRefutation.lean](lean/ZhuRefutation.lean) constructs a six-vertex
digraph in which every vertex has two incoming and two outgoing arcs and every
vertex is reachable from every other. Its projector graph has three C4
components. Thus the graph contradicts Theorem 1(c3): 3 > 6/4. The Lean
proofs check that eight code choices yield perfect
matchings. Under the paper's examples' convention that codes are identified
by permuting identical components, the codes have four different weights
0, 1, 2, 3, whereas n/2 = 3. The proof also checks that two choices
give different cycle outcomes in the inverse digraph. The reproducible
enumeration in [projector_witness.py](../../../../experiments/issue580/projector_witness.py)
computes every matching and its incidence rank.

**Classification: concrete refutation of Theorem 1(c3), conditional result
for Lemma 4.** The paper does not define "isomorphic" precisely enough to
prove that its intended unlabeled quotient is exactly this code-permutation
quotient. A complete refutation of the
algorithm would also have to formalize the update operator in equations
(10–11), the claimed monotonicity of the rank function, and the rule for
selecting a representative from each class. None of those claims is proved
or disproved here.

The [Rocq file](rocq/ZhuRefutation.v) checks the same finite graph, three
four-cycle components, code classes, and different cycle outcomes. Neither
formalization defines the
paper's rank-greedy update algorithm.
