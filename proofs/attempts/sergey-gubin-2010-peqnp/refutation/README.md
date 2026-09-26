# Gubin 2010 LP refutation audit

The old Lean and Rocq files were inconsistent. They treated every point as an
LP vertex and every vertex order as a tour, then asserted incompatible facts
as axioms. The [reproduction](../../../../experiments/issue578/README.md)
shows that both proof assistants accepted proofs of `False` from those files.
Those assertions and their dependent theorems have been withdrawn.

## Counterexample to the paper

The new [Lean](lean/GubinPaperCounterexample.lean) and
[Rocq](rocq/GubinPaperCounterexample.v) files transcribe Gubin's arXiv
version [cs/0610042v3][gubin], equations (1.8) and (1.9), for six vertices.
They check all the equalities, nonnegativity bounds, and compatibility zeros
using exact rational arithmetic.

The graph is the disjoint union of directed cycles `0→1→2→0` and
`3→4→5→3`. It has no Hamiltonian tour. An explicit LP point nevertheless
satisfies every constraint. Its diagonal variables are `y(j,ν) = 1/6`. For
distinct position indices `i,j` and distinct graph vertices `a,b`, its
off-diagonal variables are:

- `x(i,j,a,b) = 1/6` when `j` follows `i` and `a→b` is an edge, or when
  `i` follows `j` and `b→a` is an edge;
- `x(i,j,a,b) = 1/18` when the position indices are nonadjacent and `a,b`
  lie in different components;
- `x(i,j,a,b) = 0` otherwise.

The theorems `paper_correspondence_fails` prove feasibility and the absence
of a tour in both systems. Since there are no solution grids for this graph,
their convex hull is empty. The feasible LP point therefore refutes the
paper's Theorem 1.2, which equates that convex hull with the region defined
by (1.8) and (1.9). This witness is independent of the historically cited
Hofman and Rizzi refutations.

The older [Lean](lean/GubinRefutation.lean) and
[Rocq](rocq/GubinRefutation.v) audit files also prove two illustrative facts
about separate small LPs: coordinate asymmetry does not imply integrality,
and an integral LP vertex alone does not imply a tour correspondence. Those
examples are not instances of Gubin's LP. Their coordinate symmetry predicate
does not model Yannakakis' graph relabeling action; the paper counterexample
does not need that action.

## Verification

```sh
python3 experiments/issue578/check_paper_lp.py
python3 scripts/check_gubin_audit.py
lean proofs/attempts/sergey-gubin-2010-peqnp/refutation/lean/GubinPaperCounterexample.lean
rocq compile proofs/attempts/sergey-gubin-2010-peqnp/refutation/rocq/GubinPaperCounterexample.v
```

[gubin]: https://arxiv.org/pdf/cs/0610042
