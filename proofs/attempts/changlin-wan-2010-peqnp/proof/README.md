# Forward Proof Formalization: Changlin Wan (2010)

This directory contains the formal proof attempt following Wan's approach as faithfully as possible.

## Contents

- `lean/WanProof.lean` - Lean 4 formalization
- `rocq/WanProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture Wan's claimed proof steps:

1. **Section 2 - Recursive TM Definition**: The paper defines a sequence of all Turing machines via a "recursive definition." Standard computability theory does show TMs are enumerable, but this doesn't help with complexity.

2. **Section 3 - Class D**: The collection of all decidable languages with subset/reduction partial order.

3. **Section 4 - Language Up**: Defined as the union of all languages in class D (= union of all decidable languages).

4. **Section 5 - Main Claims**:
   - **Claim 5.1** (P ⊆ Up): Any language in P is decidable, so contained in Up. **TRUE** - proven in formalizations.
   - **Claim 5.2** (Up ⊆ NP): The "recursive TM" simulates any TM polynomially. **FALSE** - not proven.
   - **Claim 5.3** (Up ⊆ P): The recursive TM decides Up in polynomial time. **FALSE** - the fatal gap.

## The Attempted Proof Logic

Wan's argument proceeds:

1. **Enumerate all TMs**: Construct a sequence TM₁, TM₂, ... containing all valid TMs
2. **Define Up**: The union of all languages in this sequence (= union of all decidable languages)
3. **Claim P ⊆ Up**: Every P-language appears in the sequence, so is in Up
4. **Claim Up ⊆ NP**: The "recursive TM" can simulate any TM in polynomial time (asserted without proof)
5. **Claim Up ⊆ P**: The recursive TM decides Up in polynomial time (asserted without algorithm)
6. **Conclusion**: P = Up = NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps:

1. **`up_subset_np`**: Claim that Up ⊆ NP - no valid proof exists for this
2. **`up_in_P`**: Claim that Up ∈ P - this is the fatal gap; no algorithm is provided
3. **`wan_main_theorem`**: The P = NP conclusion - depends on the false claims above

## The Core Error

The proof fails at Claim 5.3 (`up_in_P`):
- The paper claims Up can be decided in polynomial time
- But Up is the union of ALL decidable languages
- Every natural number x is in Up (since the singleton language {x} is decidable)
- Therefore Up = ℕ (all natural numbers), which IS trivially in P
- But this makes the construction vacuous - it doesn't prove P = NP

See the `../refutation/` directory for the formal proof that Up = ℕ.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Description of the original proof
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
