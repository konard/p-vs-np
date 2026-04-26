# Refutation: Malinina 2012

This directory contains the formal refutation of Malinina's claimed independence proof for P vs NP.

## Contents

- `lean/MalininaRefutation.lean` - Lean 4 refutation
- `rocq/MalininaRefutation.v` - Rocq refutation

## Summary of Errors

Malinina's 2012 argument fails for six distinct reasons:

### Error 1: Conflation of Undecidability and Independence

The halting problem is **computationally undecidable** (no algorithm solves it), while Gödel independence is **proof-theoretically independent** (no proof derives it). These are distinct:

- A statement can be computationally hard yet provable/refutable in ZFC
- Independence from ZFC means both the statement and its negation are consistent with ZFC
- P vs NP is about algorithm existence, not about self-referential provability

### Error 2: The Algorithm A Construction is Circular

Algorithm A is supposed to "invert" any polynomial-time machine M on NP instances:
- To invert M, A must find a case where M fails
- Finding such a case for an NP-complete problem *is itself* NP-hard
- A cannot find distinguishing instances in polynomial time unless P = NP
- The construction assumes what it is trying to disprove

### Error 3: Misapplication of Gödel's Theorem

For Gödel incompleteness to apply, the statement must:
1. Be expressible as an arithmetic sentence
2. Have self-referential structure (encoding its own unprovability)

P ≠ NP is expressible as an arithmetic sentence, but it does NOT encode its own unprovability — it says something about the existence of polynomial-time algorithms. Gödel's theorem does not apply without this self-referential structure.

### Error 4: The "Symmetry" Argument Does Not Hold

Malinina claims "by symmetry" that ZFC also cannot prove P = NP. But:
- The argument for P ≠ NP used a specific construction (algorithm A inverts P-algorithms)
- No analogous construction is given for P = NP
- The two directions are structurally different; "symmetry" is not justified

### Error 5: No Model-Theoretic Argument

Valid independence proofs (like Cohen's for CH) require:
1. A model of ZFC where the statement is true
2. A model of ZFC where the statement is false
3. Verification that both models satisfy ZFC axioms

Malinina provides none of these.

### Error 6: Absoluteness Issues

Many complexity-theoretic notions are **absolute** across set-theoretic models:
- The statement "there exists a polynomial-time algorithm for SAT" may have the same truth value in all models of ZFC that agree on the natural numbers
- If P vs NP is absolute, independence is impossible
- Malinina does not address this well-known obstacle

## What the Formalizations Show

The refutation formalizations demonstrate:
- ✅ The precise statement of each error
- ✅ Why the algorithm construction is circular
- ✅ Why Gödel's theorem requires self-referential structure
- ✅ What a valid independence proof would require
- ✅ Why absoluteness makes independence unlikely

## See Also

- [`../README.md`](../README.md) - Full error analysis
- [`../proof/README.md`](../proof/README.md) - Where the forward proof breaks down
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - The reconstructed proof text
