# Forward Proof Formalization: Gubin 2010

This directory contains the forward formalization of Sergey Gubin's 2010 attempted proof of P = NP via polynomial-sized asymmetric LP formulation of the ATSP polytope.

## Contents

- `lean/GubinProof.lean` - Lean 4 formalization of the proof structure
- `rocq/GubinProof.v` - Rocq (Coq) formalization of the proof structure

## What These Formalizations Capture

The formalizations attempt to capture Gubin's proof strategy:

1. **ATSP Definition**: The Asymmetric Traveling Salesman Problem as an NP-complete problem
2. **LP Formulation**: Construction of a polynomial-sized linear program for ATSP
3. **Asymmetric Construction**: The formulation being asymmetric (distinct from Yannakakis' symmetric barrier)
4. **The Critical Claim**: Correspondence between LP extreme points and ATSP tours
5. **The P = NP Implication**: How the argument would conclude P = NP if the claim held

## The Attempted Proof Logic

Gubin's argument proceeds:

1. **Define ATSP**: The Asymmetric Traveling Salesman Problem on directed graphs
2. **Construct LP formulation**: Create a polynomial-sized linear program (O(n^9) variables, O(n^7) constraints)
3. **Claim asymmetry**: The formulation is asymmetric, so Yannakakis' theorem does not directly apply
4. **Claim correspondence** (CRITICAL): Extreme points of the LP polytope correspond to valid ATSP tours
5. **Apply LP solvability**: Since LP is in P, solve the LP in polynomial time
6. **Conclude P = NP**: If ATSP ∈ P and ATSP is NP-complete, then P = NP

## Key Aspects of the Construction

### The LP/ILP Gap

The fundamental issue Gubin must address:
- Linear Programming (LP): Allows continuous/fractional solutions, solvable in polynomial time
- Integer Linear Programming (ILP): Requires integer solutions, NP-complete
- The gap between LP and ILP is where the hardness lies

### Yannakakis' Barrier

Yannakakis (1991) proved that:
- Symmetric extended formulations for TSP must have exponential size
- Gubin claims his asymmetric formulation avoids this barrier

### The Integrality Requirement

For the argument to work, Gubin needs:
- All extreme points of the LP polytope are integral (integer coordinates)
- Each integral extreme point corresponds to exactly one valid ATSP tour
- Every valid ATSP tour corresponds to some extreme point

**This is the unproven step.**

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at critical points:

1. **The integrality claim**: Gubin does not prove that extreme points are integral
2. **The correspondence claim**: Gubin does not prove that integral extreme points correspond to tours
3. **The NP-completeness reduction**: Formalizing the full reduction is beyond the scope

These placeholders mark locations where the argument cannot be completed without the unproven claims.

## Mathematical Validity vs Logical Validity

The formalization shows:

- **The structure is valid**: If integrality held, the argument would work
- **The LP construction is well-defined**: A polynomial-sized asymmetric LP can be defined
- **The critical premise is unproven**: The integrality/correspondence claim is assumed, not derived
- **The premise is false**: Rizzi (2011) refuted the claim

## Relation to the Refutation

See [`../refutation/README.md`](../refutation/README.md) for a detailed explanation of why:
- Asymmetry alone does not imply integrality
- LP polytopes can have fractional extreme points
- The LP/ILP gap is a fundamental barrier
- Rizzi's 2011 refutation demonstrates failure of the correspondence

## The Lesson

Many P = NP attempts follow this pattern:
1. Construct a polynomial-sized optimization formulation
2. Claim the formulation captures the combinatorial structure
3. Infer P = NP from the formulation's solvability
4. Fail to prove the crucial structural property (integrality, correspondence, etc.)

The formalization separates the valid structural argument from the unproven premise.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt and error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Detailed explanation of why the proof fails
