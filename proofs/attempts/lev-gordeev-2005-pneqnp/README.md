# Formalization: Lev Gordeev (2005) - P≠NP

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 24 (from Woeginger's list)
- **Author**: Lev Gordeev
- **Year**: Summer 2005
- **Claim**: P ≠ NP
- **Status**: Incomplete/Flawed
- **Source**: [Woeginger's P vs NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), Entry #24

## Overview

In Summer 2005, Lev Gordeev presented an approach to prove that P is not equal to NP. The proof was explicitly stated to be incomplete at the time, with Gordeev claiming that what remained was "technical work along the lines of traditional combinatorics." Several papers were made available from his web page at the University of Tuebingen (Germany), including "Proof-sketch: Why NP is not P."

Gordeev later continued this line of work, culminating in a 2020 arXiv preprint (arXiv:2005.00809) claiming to prove P ≠ NP. However, this proof was found to contain a critical error.

## The Main Argument

### Proof Strategy

Gordeev's approach attempts to prove P ≠ NP by:

1. **Target Problem**: Focusing on the CLIQUE problem, a known NP-complete graph-theoretic problem
2. **Circuit Lower Bounds**: Attempting to prove exponential lower bounds for De Morgan Normal (DMN) circuits computing CLIQUE
3. **Reduction**: Since CLIQUE is NP-complete, proving it's not in P would imply P ≠ NP

### Key Technical Approach

The proof strategy relies on:

- **De Morgan Normal (DMN) Circuits**: A computational model using AND, OR, and NOT gates
- **Approximation Method**: Attempting to approximate circuit inputs to establish lower bounds
- **Combinatorial Arguments**: Using "traditional combinatorics" to complete the technical details

### Main Claim

If successful, the proof would show:
- CLIQUE cannot be solved in polynomial time by any deterministic Turing machine
- This "upgrades the well-known partial result that claims only monotone unsolvability"
- Since CLIQUE is NP-complete, this would imply P ≠ NP

## The Error in the Proof

### Critical Flaw Identified

The proof contains a **crucial mistake in Lemma 12**, as identified by David Narváez and Patrick Phillips in their 2021 analysis (arXiv:2104.07166, "On Lev Gordeev's 'On P Versus NP'").

### Specific Technical Error

**The Problem**: Gordeev's approximation method **only approximates operations over positive circuit inputs**, failing to account for negated inputs.

**Why This Matters**:
- To establish lower bounds for De Morgan Normal (DMN) circuits, one must approximate **both** positive and negated inputs
- DMN circuits use NOT gates, meaning negated inputs are fundamental to the computation model
- By only handling positive inputs, the approximation technique is fundamentally incomplete

**Impact**: The entire proof strategy collapses because:
1. The lower bound argument depends on the approximation method
2. The approximation method is incomplete (missing negated inputs)
3. Without a complete approximation, the lower bound cannot be established
4. Therefore, the claim that CLIQUE ∉ P remains unproven

### Historical Context

This is not an isolated error but represents a common challenge in circuit complexity:
- Establishing lower bounds for **general circuits** is notoriously difficult
- Exponential lower bounds exist for **restricted models** (e.g., monotone circuits)
- Gordeev's attempt to extend techniques to full DMN circuits failed due to insufficient handling of negation

## Formalization Goals

This directory contains formalizations in three proof assistants (Coq, Lean, Isabelle) that:

1. **Encode the proof structure**: Formalize the definitions of CLIQUE, DMN circuits, and the approximation method
2. **Identify the gap**: Make explicit where the proof fails (the incomplete approximation in Lemma 12)
3. **Demonstrate incompleteness**: Show that the proof does not establish P ≠ NP

### What We Formalize

- **CLIQUE Problem**: Formal definition of the graph clique decision problem
- **De Morgan Normal Circuits**: Model of circuits with AND, OR, NOT gates
- **Input Approximation**: The approximation method used in the proof
- **The Gap**: Explicit statement that negated inputs are not handled
- **Incompleteness**: Proof that the argument is insufficient

### What We Do NOT Claim

- We do **not** claim to prove P ≠ NP
- We do **not** claim Gordeev's overall strategy is impossible
- We do **not** claim the approximation method cannot be extended

We **only** formalize the known incomplete/flawed aspects of this specific proof attempt.

## Implementation Status

### Lean 4 (`lean/GordeevProof.lean`)
- ✅ CLIQUE problem definition
- ✅ DMN circuit model
- ✅ Input approximation framework
- ✅ Gap identification: missing negated input handling
- ✅ Incompleteness proof

### Coq (`coq/GordeevProof.v`)
- ✅ CLIQUE problem definition
- ✅ DMN circuit model
- ✅ Input approximation framework
- ✅ Gap identification: missing negated input handling
- ✅ Incompleteness proof

### Isabelle/HOL (`isabelle/GordeevProof.thy`)
- ✅ CLIQUE problem definition
- ✅ DMN circuit model
- ✅ Input approximation framework
- ✅ Gap identification: missing negated input handling
- ✅ Incompleteness proof

## Key Insights from This Formalization

### 1. Barrier Awareness
This proof attempt faces the **Natural Proofs barrier** (Razborov-Rudich, 1997):
- The approximation method, if it worked, would be "natural" in the technical sense
- Natural proof techniques cannot establish super-polynomial circuit lower bounds (under cryptographic assumptions)
- Gordeev's incomplete handling of negated inputs is symptomatic of deeper barriers

### 2. Circuit Complexity Gap
The gap between what we can prove for **restricted circuits** vs. **general circuits** is vast:
- Monotone circuits: Exponential lower bounds known (Razborov 1985)
- General circuits: Best known ~3.1n - o(n) gates (Li & Yang, STOC 2022)
- DMN circuits: Still far from super-polynomial bounds needed for P ≠ NP

### 3. Importance of Formal Verification
This formalization demonstrates:
- Informal proof sketches can hide critical gaps
- Formal verification forces explicit handling of all cases
- The gap (missing negated inputs) becomes immediately apparent in formal logic

## References

### Primary Sources
- **Woeginger, G.** (continuously updated). "The P versus NP page." Entry #24.
  - URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

- **Gordeev, L.** (2020). "On P Versus NP." arXiv:2005.00809
  - URL: https://arxiv.org/abs/2005.00809

### Refutation
- **Narváez, D. & Phillips, P.** (2021). "On Lev Gordeev's 'On P Versus NP'." arXiv:2104.07166
  - URL: https://arxiv.org/abs/2104.07166
  - **Key Finding**: "Gordeev makes a crucial mistake in Lemma 12, where he only approximates operations over positive circuit inputs"

### Related Work on Barriers
- **Razborov, A. & Rudich, S.** (1997). "Natural Proofs." *Journal of Computer and System Sciences*, 55(1), 24-35.
  - DOI: 10.1006/jcss.1997.1494

- **Razborov, A.** (1985). "Lower bounds on the monotone complexity of some Boolean functions." *Soviet Mathematics Doklady*, 31, 354-357.

- **Li, K. & Yang, K.** (2022). "Improved Bounds for the Complexity of Boolean Functions." *STOC 2022*.

### Background on CLIQUE and NP-Completeness
- **Karp, R.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, 85-103.
  - CLIQUE is one of Karp's original 21 NP-complete problems

## Educational Value

This formalization serves several purposes:

1. **Historical Documentation**: Preserves the structure and failure mode of a real P vs NP attempt
2. **Barrier Illustration**: Concretely demonstrates how Natural Proofs barrier manifests
3. **Formalization Practice**: Provides template for formalizing circuit lower bound arguments
4. **Research Guidance**: Shows what doesn't work, helping future researchers avoid similar pitfalls

## Verification

To verify the formalizations:

```bash
# Lean 4
cd lean
lake build

# Coq
cd coq
coqc GordeevProof.v

# Isabelle/HOL
cd isabelle
isabelle build -D .
```

## License

This formalization is provided for educational and research purposes. See repository [LICENSE](../../../LICENSE).

## Acknowledgments

- **Lev Gordeev**: For the original proof attempt and making materials available
- **David Narváez & Patrick Phillips**: For identifying the specific error in Lemma 12
- **Gerhard Woeginger**: For maintaining the comprehensive P vs NP attempts list

---

**Note**: This formalization is part of a larger effort (#44) to formally test all P vs NP proof attempts. The goal is educational: to understand why these proofs fail and what barriers exist to solving this fundamental problem.

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P_VS_NP_TASK_DESCRIPTION.md](../../../P_VS_NP_TASK_DESCRIPTION.md)
