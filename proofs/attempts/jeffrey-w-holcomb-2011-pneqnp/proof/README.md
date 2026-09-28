# Forward Proof Formalization: Holcomb 2011

This directory contains the formal proof attempt following Holcomb's approach as faithfully
as possible, given that the original papers are no longer accessible.

## Contents

- `lean/HolcombProof.lean` - Lean 4 formalization
- `rocq/HolcombProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to follow the proof structure described in Woeginger's page and
based on the known key paper title "Just How Random Are Your Answers?":

1. **Basic definitions**: P, NP using standard complexity-theoretic definitions
2. **The claimed key concept**: Several attempted interpretations of "stochastic answer"
3. **Step 1**: The claim that problems in P do NOT have stochastic answers
4. **Step 2**: The claim that some NP problem HAS stochastic answers
5. **The conclusion**: P ≠ NP derived from steps 1 and 2

## Following the Original Proof Text

Each section of the formalization corresponds to a step in Holcomb's claimed argument:

### From ORIGINAL.md, Step 1: Define "stochastic answer"

> Holcomb claimed to identify a property of the answers to problems in NP \ P that
> distinguishes them from problems in P. This property was described as "stochastic."

The formalization attempts multiple interpretations of this concept, each of which fails:

- **Interpretation A**: Stochastic = has many possible witnesses (doesn't work: P problems
  can have many solutions too)
- **Interpretation B**: Stochastic = answers are unpredictable in some distribution (doesn't
  work: decision problems have deterministic answers)
- **Interpretation C**: Abstract axiom (what the proof reduces to without a definition)

### From ORIGINAL.md, Step 2: P problems have no stochastic answers

> Problems in P have deterministic, efficiently computable answers.

This is taken as an axiom in the formalization, since without a formal definition of
"stochastic answer," it cannot be proven.

### From ORIGINAL.md, Step 3: NP \ P problems have stochastic answers

> Problems like SAT, where we cannot efficiently determine the answer, have stochastic
> character.

This is also taken as an axiom in the formalization for the same reason.

### From ORIGINAL.md, Step 4: Conclude P ≠ NP

> If P = NP, then every NP problem would be in P. But P problems don't have stochastic
> answers while some NP problems do. Contradiction.

This step is actually formalizable — IF the axioms held, the conclusion would follow.
The `holcomb_claimed_proof` theorem is proven in both Lean and Rocq, demonstrating that
the proof STRUCTURE is sound — the problem is with the premises (undefined concepts, unjustified axioms).

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the
critical gaps where Holcomb's argument fails:

1. **No definition of StochasticAnswer**: The key concept is declared as an axiom
   because no formal definition was provided in the original proof
2. **No proof of P_problems_not_stochastic**: Cannot prove without a definition
3. **No proof of some_NP_problem_is_stochastic**: Cannot prove without a definition
4. **The gap theorem**: `holcomb_proof_gap` is admitted because we cannot prove properties
   of an undefined concept

## The Core Error

The proof is **formally valid in structure** but **materially empty**:

```
StochasticAnswer := ??? (undefined)
P_problems_not_stochastic := axiom (unproven)
some_NP_problem_is_stochastic := axiom (unproven)
⟹ holcomb_claimed_proof: ¬ P_equals_NP  (formally proven from axioms)
```

This is like claiming "All purple problems are hard, some NP problems are purple, therefore
P ≠ NP" — the logical structure is valid but "purple" is undefined and the premises are
not established.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt and error explanation
- [`../ORIGINAL.md`](../ORIGINAL.md) - Reconstructed description of the original proof
- [`../refutation/README.md`](../refutation/README.md) - Why the proof fails
