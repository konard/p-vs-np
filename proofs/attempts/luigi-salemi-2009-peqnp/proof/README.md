# Salemi (2009) - Forward Proof Formalization

This directory contains the formalization of Salemi's P=NP proof attempt, following the approach described in the original paper.

## Structure

The formalization follows Salemi's method for solving 3SAT in polynomial time:

1. **CI3Sat Construction** - Complementation of Inverse 3SAT (Theorems 1-3)
2. **Reduction Operation** - Simplifying CI3Sat while preserving solutions (Theorem 6)
3. **Saturation Operation** - Iterative deletion of redundant AClausolas (Theorem 8)
4. **Constructive Proof** - Building solutions from saturated CI3Sat (Theorem 11)
5. **Main Claim** - Polynomial-time 3SAT solver implies P=NP (Theorem 12)

## Formalizations

### Lean 4 (`lean/Salemi3SAT.lean`)

Formalizes the core definitions and operations:
- `Literal`, `Clause`, `AClausola`, `Formula3SAT`
- `CI3Sat` structure with `rows` and `complete` property
- `reduction` and `saturation` operations
- Complexity claims and error axioms

Uses `sorry` placeholders where:
- The proof is incomplete in the original paper
- The construction requires exponential complexity
- Circular reasoning prevents completion

### Rocq/Coq (`rocq/Salemi3SAT.v`)

Parallel formalization in Coq with:
- Mutual inductive definitions for `literal` and `fin`
- Record types for `clause`, `aclausola`, `formula_3sat`
- Operations following the paper's algorithm

## Known Issues

The formalization highlights critical errors:

1. **Complexity Error**: Saturation claimed O(n^15), but iteration bound not proven
2. **Circular Reasoning**: Theorem 11 assumes properties Saturation should guarantee
3. **Missing Termination**: Construction algorithm has no polynomial time proof

See `../refutation/` for formal refutations of these errors.

## Notes

- Uses only core Lean 4 (no Mathlib) and standard Coq libraries
- `sorry`/`Admitted` marks intentionally incomplete proofs
- Comments explain why specific parts cannot be proven
