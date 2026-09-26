# Audit of the Gubin 2010 formalization

The former Lean and Rocq files were inconsistent. They described an LP only by
variable and constraint counts, treated every point as a vertex and every vertex
order as a tour, and asserted both asymmetry and a published refutation as
axioms. In Lean, those assumptions proved `False`. In Rocq, `isIntegral` was
defined as `True` while an axiom supplied a point satisfying `~ isIntegral`.

The revised files withdraw those axioms and all theorems derived from them.
They define feasibility, extreme points, integral coordinates, valid directed
tours, an explicit tour encoding, and coordinate symmetry. Two small LPs then
establish limited, fully proved facts in both systems:

1. The equations `x₀ = 1/2` and `x₁ = 0` have a fractional extreme point. The
   feasible region is not invariant under swapping its two coordinates.
2. The equation `x₀ = 0` has an integral extreme point even when paired with a
   directed graph with no tour. Consequently, LP size and integrality alone do
   not imply the abstract tour/vertex correspondence.

These are **illustrative countermodels**, not instances of Gubin's LP. The
`IsCoordinateSymmetric` / `isCoordinateSymmetric` predicates test permutations
of LP coordinates. Yannakakis' symmetry condition concerns graph vertex
relabelings and their induced action on extended variables. No such action for
Gubin's construction has been encoded here.

Neither formal file proves that the correspondence in [Gubin's paper][gubin]
is false, nor does it encode [Hofman's published counterexamples][hofman] for
the paper. A paper level refutation still requires the original inequalities,
the projection to ATSP tours, a vertex relabeling action, and a concrete
counterexample checked against those inequalities. Until then, the historical
refutation remains a literature claim rather than a theorem in this repository.

## Verification

```sh
lean proofs/attempts/sergey-gubin-2010-peqnp/refutation/lean/GubinRefutation.lean
rocq compile proofs/attempts/sergey-gubin-2010-peqnp/refutation/rocq/GubinRefutation.v
python3 scripts/check_gubin_audit.py
```

The old contradictions and reproduction commands are recorded in
[`experiments/issue578/README.md`](../../../../experiments/issue578/README.md).

[gubin]: https://combinatorialpress.com/article/jcmcc/Volume%20074/vol-074-paper%2024.pdf
[hofman]: https://arxiv.org/abs/cs/0610125
