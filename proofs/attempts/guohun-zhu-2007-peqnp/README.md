# Guohun Zhu (2007): P=NP attempt

**Attempt ID:** 40 · **Source:** [arXiv:0704.0309v3](https://arxiv.org/abs/0704.0309v3),
“The Complexity of HCP in Digraphs with Degree Bound Two”

Zhu maps a degree-two directed graph D to a balanced bipartite projector
graph G. Theorem 2 uses a perfect matching M whose inverse image has incidence
rank n−1 to identify a Hamiltonian cycle. Lemma 4 gives an exponential count
for **labeled** perfect matchings but an n/2 upper bound for **unlabeled**
ones. Theorem 3 then claims an O(n⁴) algorithm using matching updates and
rank checks; the later theorems derive P=NP.

## Audited result

The [Lean](refutation/lean/ZhuRefutation.lean) and
[Rocq](refutation/rocq/ZhuRefutation.v) refutations now use a concrete
six-vertex Γ digraph. Each vertex has two incoming and outgoing arcs, and the
graph is strongly connected. Its projector graph has three C4 components and
eight labeled perfect matchings. This directly contradicts Theorem 1(c3),
which bounds the number of C4 components by n/4=1 (with n=6). The
code-permutation convention illustrated in Zhu's paper gives four code-weight
classes, more than the separate Lemma 4 bound n/2=3. Different
matchings also produce different cycle outcomes in the inverse digraph.
The [enumeration script](../../../experiments/issue580/projector_witness.py)
prints all eight matchings and their incidence ranks.

**Evidence level: concrete refutation of Theorem 1(c3); conditional result for
Lemma 4.** The paper does not precisely define the isomorphism relation used
to form its unlabeled classes. The four-class counterexample addresses the
convention suggested by its examples, not every possible quotient. This
audit does not establish that the update equations (10–11) miss a Hamiltonian
cycle: their operator, ordering, and representative selection still require a
formal specification and proof. The simple
inequality 2^k > 2k is only an arithmetic illustration and does not by
itself refute the unlabeled count.

See [the refutation notes](refutation/README.md) for the exact proposition
and limits. The [forward files](proof/README.md) are sketches with
unproved premises. The original text is archived as
[Markdown](ORIGINAL.md) and [PDF](ORIGINAL.pdf).
