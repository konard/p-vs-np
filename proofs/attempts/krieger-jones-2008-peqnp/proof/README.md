# Forward Proof Formalization

This folder contains the formalization of Krieger & Jones' attempted proof that P=NP.

## The Claim

Krieger and Jones (2008) claimed to have developed a polynomial-time algorithm for detecting Hamiltonian circuits in undirected graphs. Since the Hamiltonian circuit problem is NP-complete, they argued this proves P=NP.

## Formalization Approach

The formalizations in this folder follow the structure of the original patent application's argument:

1. **Setup**: Define complexity classes P, NP, and NP-completeness
2. **Graph Theory**: Define graphs, paths, and Hamiltonian circuits
3. **The Claimed Algorithm**: Formalize the matrix-based approach from the patent
4. **The Implication**: Show that IF such an algorithm existed with the claimed properties, THEN P=NP would follow

## The Gap

The formalizations use `sorry` (Lean) and `Admitted` (Rocq) to mark the critical gap: **no valid polynomial-time algorithm is actually provided**. The patent application describes matrix operations but:

- Does not provide a complete, unambiguous algorithm specification
- Does not prove the algorithm always produces correct answers
- Does not rigorously prove polynomial time complexity
- Has not been validated by peer review
- Is not accepted by the theoretical computer science community

## Key Insight

The conditional implication is correct:
```
IF [polynomial-time Hamiltonian circuit algorithm exists]
THEN [P = NP]
```

However, the antecedent (the IF part) has not been established. This is a common pattern in failed P vs NP attempts: the logical structure is sound, but a crucial premise is missing or invalid.

## See Also

- `../refutation/` - Formal refutations of specific claims
- `../original/` - The original patent application text
