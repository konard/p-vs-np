# Refutation of Singh Anand (2006)

This directory contains formal refutations of Singh Anand's 2006 P ≠ NP proof attempt.

## Contents

- `lean/SinghAnandRefutation.lean` - Lean 4 refutation
- `rocq/SinghAnandRefutation.v` - Rocq refutation

## The Core Error: Provability Does Not Eliminate Non-Standard Models

### Singh Anand's Claim

The paper proves that the formula:
```
G(x) := x = 0 ∨ ∃y, x = S(y)
```
is provable in PA by induction, then concludes that PA has no non-standard models.

### Why This Is Wrong

**Gödel's Completeness Theorem** states: if a formula φ is provable in PA, then φ is true in **every** model of PA.

This means proving (∀x)G(x) in PA tells us that G(x) holds in ALL models—both standard and non-standard. It does not tell us that only the standard model exists.

**Non-standard elements satisfy G(x)**:

In a non-standard model, the non-standard elements form "infinite chains" extending beyond the standard natural numbers. Each non-standard element ω has a predecessor ω - 1 (also a non-standard element), so:

```
ω = S(ω - 1)   →   G(ω) holds (ω is a successor)
```

The formula G(x) is perfectly consistent with non-standard models. It merely says every element is either 0 or a successor—which is true for non-standard elements too (they are successors of other non-standard elements).

### The Contradiction

If Singh Anand's reasoning were correct, it would mean:

1. (∀x)G(x) is provable in PA.
2. (∀x)G(x) provable → PA has no non-standard models.

But we know (from established mathematics) that non-standard models of PA exist. This is guaranteed by:

- **Gödel's Incompleteness Theorem**: PA cannot pin down the natural numbers uniquely; it has models of different cardinalities.
- **Löwenheim-Skolem Theorem**: Any consistent first-order theory with an infinite model has models of every infinite cardinality.
- **Compactness Theorem**: Adding "there exists an element greater than every standard numeral" is consistent with PA, yielding non-standard models.

Therefore step 2 above is simply false.

## Two Key Theorems in the Refutation

### Theorem 1: Singh Anand's Claim Leads to Contradiction

If Singh Anand's inference were valid:
- We could show non-standard models do not exist.
- But non-standard models do exist (known mathematical fact).
- Contradiction!

### Theorem 2: G(x) Holds in Non-Standard Models

The formula (∀x)G(x) is satisfied in non-standard models, demonstrating that proving it does not eliminate such models. This directly refutes the key inference in the paper.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown reconstruction of the original paper
- [`../proof/README.md`](../proof/README.md) - Forward proof formalization
