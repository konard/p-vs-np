# Forward Proof Formalization: Jiang 2009

This directory contains the formal proof attempt following Jiang's approach as faithfully as possible.

## Contents

- `lean/JiangProof.lean` - Lean 4 formalization
- `rocq/JiangProof.v` - Rocq (Coq) formalization

## What These Formalizations Capture

The formalizations attempt to capture the structure of Jiang's argument:

1. **Problem Definitions**: Basic complexity theory (P, NP, NP-completeness), Hamiltonian Circuit, and the MSP problem
2. **The Reduction**: Jiang's claimed polynomial-time reduction from HC to MSP
3. **The Algorithm**: Jiang's claimed polynomial-time algorithm for MSP
4. **The Conclusion**: How these two claims together would imply P = NP

## The Attempted Proof Logic

Jiang's argument proceeds:

1. **Define MSP**: Introduce the Multistage Graph Simple Path problem
2. **Reduce HC → MSP**: Show HC polynomially reduces to MSP in O(n²) or O(n³) time
3. **Solve MSP**: Claim a polynomial-time algorithm for MSP (O(n³) or O(n⁴))
4. **Conclude**: HC ∈ P → P = NP (since HC is NP-complete)

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Jiang's argument fails:

1. **MSP Definition Gap**: The MSP problem is axiomatized because Jiang's definition is vague — we cannot formalize something that is not rigorously defined
2. **Reduction Correctness Gap**: The claimed correctness of the HC → MSP reduction (`jiang_reduction_correctness_claim`) is marked as an axiom — no rigorous proof is provided in the paper
3. **Algorithm Correctness Gap**: The correctness of Jiang's MSP algorithm (`jiang_MSP_algorithm_correctness_claim`) is marked as an axiom — the paper only provides experimental validation, not a mathematical proof
4. **Complexity Gap**: No formal proof that the algorithm is truly polynomial (the claimed O(n⁴) bound is asserted, not derived)

## The Core Error (Formalized)

The fundamental issue captured in the formalization:

**IF** MSP is actually in P (not NP-complete as assumed), **THEN**:
- The reduction HC ≤_p MSP is trivially possible (any language reduces to a language in P that accepts all strings)
- But this reduction does not help solve HC
- Therefore, the argument breaks down

The formalizations show that `jiang_complete_argument` depends on critical unproven axioms about:
- MSP's complexity class
- The correctness of the reduction
- The correctness and complexity of the algorithm

## See Also

- [`../original/README.md`](../original/README.md) - Description of Jiang's approach
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Why the proof fails
