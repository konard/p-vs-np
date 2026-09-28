# Forward Proof Formalization

This directory contains the forward proof formalization following Carlos Barron-Romero's
argument structure from arXiv:1006.2218v1.

## What We Formalize

The forward proof follows the paper's reasoning as faithfully as possible:

1. **Paper's definitions**: NPProblem, search space, "checking" (Barron-Romero's terminology)
2. **Proposition 1.1**: The claim that NP problems have no polynomial verification
3. **GAP/TSP analysis**: The paper's analysis of search space sizes
4. **Proposition 6.9**: 2D Euclidean TSP has polynomial checking (axiomatized — this is false)
5. **Proposition 6.12**: Arbitrary GAP has no polynomial checking (true but for wrong reason)

## Files

- `lean/BarronRomeroProof.lean` — Lean 4 formalization of the forward proof
- `rocq/BarronRomeroProof.v` — Rocq formalization of the forward proof

## Key Observation

The paper correctly shows that **finding** the optimal TSP solution requires exploring
(n-1)! possibilities, which is super-polynomial. However, this is a statement about
*solving*, not *verifying*.

Steps that can be proven:
- ✓ TSP has (n-1)! possible tours
- ✓ Algorithm 9 (exhaustive search) is not polynomial

Steps that cannot be proven (marked with `sorry`/`Admitted`):
- ✗ That Algorithm 9 is the *only* way to "check" a solution
- ✗ Proposition 6.9 (2D Euclidean TSP has polynomial algorithms — this is false)

## See Also

- [Refutation](../refutation/README.md) — Why the argument fails
- [Main README](../README.md) — Overview of the attempt
