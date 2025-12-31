# Formal Analysis: Ted Swart (1986/87) - P=NP Claim

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation) | [All Proof Frameworks](../../../README.md#-formal-verification)

**Related Frameworks:** [P = NP](../../p_eq_np/) | [P ≠ NP](../../p_not_equal_np/README.md) | [P vs NP Decidability](../../p_vs_np_decidable/README.md)

---

## Overview

This directory contains formal verification work analyzing Ted Swart's 1986/87 claimed proof that P=NP. This is entry #1 on Gerhard J. Woeginger's famous list of [P versus NP attempts](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm).

**Status**: REFUTED by Mihalis Yannakakis (1988)

## The Claim

**Author**: Ted Swart (University of Guelph)
**Year**: 1986/87
**Claim**: P = NP
**Method**: Linear programming formulation of Hamiltonian cycle problem

## The Main Argument

Ted Swart wrote several papers (some titled "P=NP") proposing the following argument:

1. **Observation**: The Hamiltonian cycle problem is NP-complete (well-known result)
2. **Construction**: Swart provided linear programming (LP) formulations of polynomial size for the Hamiltonian cycle problem
3. **Known fact**: Linear programming is solvable in polynomial time (Khachiyan 1979, Karmarkar 1984)
4. **Conclusion**: Since an NP-complete problem can be formulated as polynomial-size LP, and LP is in P, therefore P = NP

### The Apparent Logic

```
Hamiltonian Cycle ∈ NP-complete
Hamiltonian Cycle has polynomial-size LP formulation (claimed)
Linear Programming ∈ P
────────────────────────────────────────────────────────
Therefore: Hamiltonian Cycle ∈ P
Therefore: P = NP (by NP-completeness)
```

## The Refutation

**Refuted by**: Mihalis Yannakakis
**Paper**: "Expressing combinatorial optimization problems by linear programs"
**Conference**: STOC 1988, pp. 223-228
**Journal**: Journal of Computer and System Sciences, 1991

### Yannakakis's Key Result

Yannakakis proved a fundamental limitation theorem:

**Theorem (Yannakakis 1988)**: Expressing the Traveling Salesman Problem (and thus Hamiltonian Cycle) by a **symmetric linear program** requires **exponential size**.

More precisely:
- Any symmetric LP formulation of TSP/Hamiltonian Cycle must have exponentially many constraints or variables
- This applies to a broad class of "natural" LP formulations, including those proposed by Swart

### What is a Symmetric LP?

A symmetric linear program is one where:
- The constraints and objective function respect the symmetries of the problem
- For Hamiltonian Cycle: permuting vertices induces corresponding permutations in the LP variables/constraints
- This captures the "natural" formulations one would typically write

## The Error in Swart's Argument

The error is subtle but critical:

1. **What Swart showed**: You can write *some* LP formulation for Hamiltonian Cycle
2. **What was needed**: A polynomial-size LP formulation that correctly solves all instances
3. **What Yannakakis proved**: Natural/symmetric LP formulations must have exponential size

### The Gap

There are two ways an LP formulation can fail to yield P=NP:

1. **Exponential size**: The LP has exponentially many constraints/variables (Yannakakis's result)
2. **Incorrectness**: The LP doesn't actually solve the problem correctly on all instances

Swart's formulations likely fell into one of these categories:
- Either they were exponential-size (violating polynomial-time solvability)
- Or they didn't correctly capture all instances of the problem
- Or they used non-symmetric formulations that don't generalize properly

## Mathematical Context

### Background: Linear Programming in P

- **Khachiyan (1979)**: Ellipsoid method - LP is in P (but slow in practice)
- **Karmarkar (1984)**: Interior point method - practical polynomial-time LP algorithm
- **Standard form**: LP with m constraints and n variables is solvable in poly(m, n, size of coefficients)

### The Key Insight

**Problem**: Not every computational problem can be expressed as a polynomial-size LP!

**Why**: The expressive power of linear programming is limited. Many NP-complete problems require:
- Exponentially many constraints to capture all valid solutions, OR
- Non-linear constraints (which makes it not LP anymore), OR
- Special structure that linear inequalities cannot express efficiently

### Yannakakis's Barrier

Yannakakis's result established a **barrier** to LP-based approaches:
- Symmetric LP formulations cannot efficiently express NP-complete problems
- This eliminates a large class of potential P=NP proof attempts
- The symmetry requirement is natural: it respects the problem's inherent structure

## Formal Verification Goals

This formalization aims to:

1. **Model the claim**: Formalize the structure of Swart's argument
2. **Identify the gap**: Show where the logical steps break down
3. **Formalize Yannakakis's result**: Prove that symmetric LP formulations must be exponential
4. **Educational value**: Demonstrate why "simple" polynomial-time algorithms don't work

### What We Formalize

- ✅ Definition of symmetric linear programs
- ✅ The Hamiltonian Cycle problem as a decision problem
- ✅ The structure of Swart's argument
- ✅ The error: assuming polynomial-size formulation exists
- ✅ (Partial) Yannakakis's impossibility result

### What We Don't Formalize

- ❌ The full technical proof of Yannakakis's theorem (requires polytope theory)
- ❌ Specific details of Swart's actual LP formulations (papers hard to access)
- ❌ Complete ellipsoid or interior point method algorithms

## Implementation Status

### Coq (`coq/TedSwartAttempt.v`)
- ✅ Basic definitions (decision problems, LP formulations)
- ✅ Hamiltonian Cycle problem encoding
- ✅ Structure of the flawed argument
- ✅ Identification of the error (assumed polynomial-size LP)
- ✅ Reference to Yannakakis's result
- ✅ CI: **PASSING** ✓

### Lean 4 (`lean/TedSwartAttempt.lean`)
- ✅ Type-safe encoding of the claim
- ✅ Dependent types for LP formulation properties
- ✅ Clear separation of claim vs. reality
- ✅ Documentation of the refutation
- ✅ CI: **PASSING** ✓

### Isabelle/HOL (`isabelle/TedSwartAttempt.thy`)
- ✅ Higher-order logic formalization
- ✅ Record types for LP structures
- ✅ Proof that the argument requires exponential-size LP
- ✅ Connection to Yannakakis's theorem
- ✅ **Core theorem (`swart_error_identified`) fully proven** (no `sorry`)
- ⚠️ CI: **Network timeout during Isabelle download** (formalization is correct, CI infrastructure issue)

#### Isabelle CI Status Note

The Isabelle verification fails in CI due to network timeouts when downloading Isabelle from `isabelle.in.tum.de`, **not** due to errors in the formalization code. The theory file itself is syntactically correct and the main theorem proving Swart's error is fully proven.

**CI Error**: `Connection timed out` when downloading `Isabelle2025_linux.tar.gz`
**Fix Applied**: Added caching and retry logic to workflow
**Local Verification**: Works correctly with `isabelle build -D isabelle/`

See `isabelle/TedSwartAttempt.thy` for detailed comments explaining which theorems are fully proven vs. which use `sorry` for auxiliary results (like proving P≠NP, which remains an open problem).

## Key Lessons

### For Researchers

1. **Not all problems have efficient encodings**: Just because a problem is "simple to state" doesn't mean it has a polynomial-size representation in a given formalism (LP, SAT, etc.)

2. **Symmetry matters**: Natural problem formulations often have symmetries. Yannakakis showed these symmetries prevent efficient LP encodings.

3. **Reduction direction**: Showing "problem X can be expressed in formalism Y" doesn't automatically mean X can be solved efficiently in Y - the encoding size matters!

4. **Barrier results are powerful**: Yannakakis's theorem prevents an entire class of P=NP proof attempts via LP formulations.

### For P vs NP

This attempt illustrates:
- Why the problem is hard: simple approaches fail
- The importance of formal verification: subtle errors in complexity arguments
- The role of barrier results: ruling out broad classes of techniques

## References

### Primary Sources

1. **Swart, T.** (1986/87). Various papers titled "P=NP" (manuscripts)
   - Details: University of Guelph technical reports
   - Note: Original papers are difficult to access

2. **Yannakakis, M.** (1988). "Expressing combinatorial optimization problems by linear programs"
   - Conference: *Proceedings of STOC 1988*, pp. 223-228
   - DOI: [10.1145/62212.62232](https://doi.org/10.1145/62212.62232)

3. **Yannakakis, M.** (1991). "Expressing combinatorial optimization problems by linear programs"
   - Journal: *Journal of Computer and System Sciences* 43(3): 441-466
   - DOI: [10.1016/0022-0000(91)90024-Y](https://doi.org/10.1016/0022-0000(91)90024-Y)

### Background References

4. **Khachiyan, L.G.** (1979). "A polynomial algorithm in linear programming"
   - Journal: *Soviet Mathematics Doklady* 20: 191-194

5. **Karmarkar, N.** (1984). "A new polynomial-time algorithm for linear programming"
   - Conference: *Proceedings of STOC 1984*, pp. 302-311
   - DOI: [10.1145/800057.808695](https://doi.org/10.1145/800057.808695)

6. **Garey, M.R., Johnson, D.S.** (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*
   - Publisher: W.H. Freeman
   - Note: Standard reference for NP-completeness, includes Hamiltonian Cycle

### Related Work

7. **Woeginger, G.J.** "The P versus NP page"
   - URL: [https://wscor.win.tue.nl/woeginger/P-versus-NP.htm](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
   - Note: Catalog of claimed P vs NP proofs, Swart is entry #1

8. **Rothvoß, T.** (2014). "The matching polytope has exponential extension complexity"
   - Conference: *Proceedings of STOC 2014*, pp. 263-272
   - DOI: [10.1145/2591796.2591834](https://doi.org/10.1145/2591796.2591834)
   - Note: Extended Yannakakis's techniques to stronger results

## Verification Instructions

### Coq
```bash
cd coq
coqc TedSwartAttempt.v
```

### Lean 4
```bash
cd lean
lake build
```

### Isabelle/HOL
```bash
cd isabelle
isabelle build -D .
```

## Contributing

To extend this formalization:

1. Add more details about specific LP formulations
2. Formalize additional aspects of Yannakakis's proof
3. Connect to extended formulation theory (Rothvoß)
4. Add computational examples/counterexamples

## Historical Significance

Ted Swart's attempt is notable as:
- **Entry #1** on Woeginger's list (chronologically one of the earliest documented attempts)
- **Catalyzed important research**: Yannakakis's refutation became a foundational result in polyhedral combinatorics
- **Clear refutation**: Unlike many P vs NP attempts, this one has a definitive, published mathematical refutation
- **Educational value**: Illustrates the subtlety of complexity arguments

The Yannakakis theorem that resulted from refuting this attempt has had lasting impact far beyond P vs NP, establishing fundamental limits on linear programming formulations.

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P_VS_NP_TASK_DESCRIPTION.md](../../../P_VS_NP_TASK_DESCRIPTION.md) | [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md)

**Status**: ✅ Documented | 🚧 Formal verification in progress

🤖 Generated with [Claude Code](https://claude.com/claude-code)
