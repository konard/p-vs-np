# Peng Cui (2014) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: #98 (Woeginger's list)
- **Author**: Peng Cui
- **Year**: 2014 (revised 2015)
- **Claim**: P = NP
- **Paper Title**: "Approximation Resistance by Disguising Biased Distributions"
- **Source**: [arXiv:1401.6520v24](https://arxiv.org/abs/1401.6520)
- **Status**: Claimed proof contains logical errors

## Summary

In this 2014 paper (revised through 2015), Peng Cui claims to prove that P = NP. The paper attempts to show that a certain 3-XOR gap problem, which is known to be NP-hard by Chan's theorem, can be solved in polynomial time by running the Charikar & Wirth SDP algorithm for two rounds. The author concludes that since an NP-hard problem can be solved in polynomial time, P = NP.

## The Main Argument

The proof structure follows these steps:

### 1. Background: Approximation Resistance

- **Max k-CSP**: The task of satisfying the maximum fraction of constraints where each constraint involves k variables
- **Approximation Resistant CSPs**: CSPs that are NP-hard to approximate better than a random assignment (e.g., Max 3-SAT, Max 3-XOR)
- **Chan's Result (2013)**: Shows that CSPs whose support forms a subgroup with balanced pairwise independent distribution are approximation resistant

### 2. Chan's Theorem (Theorem 1 in the paper)

For arbitrarily small constant ε, it is NP-hard to distinguish:
- **Completeness**: val(P) ≥ 1 - ε
- **Soundness**: val(P) ≤ 1/2 + ε

This establishes a gap problem for 3-XOR that is NP-hard.

### 3. Cui's Construction (Section 4)

Cui considers a specific 3-XOR instance where:
- C = G₃ ∪ G₁ (where Gₘ denotes 3-tuples with exactly m ones)
- The distribution ψ = (3/4, 1/4) disguises uniform distributions over G₃ and G₁ to create a balanced pairwise independent distribution
- The constraint is a subgroup of G³

### 4. Cui's Algorithm

**The claimed polynomial-time algorithm:**

1. **Step 1**: Run Charikar & Wirth's SDP algorithm on the bi-linear form I⁽²⁾ (derived from tri-linear form I⁽³⁾) to get assignment f⁽¹⁾
2. **Step 2**: Run the SDP algorithm again on I⁽³⁾ subject to f⁽¹⁾ to get assignment f⁽²⁾
3. **Step 3**: Combine f⁽¹⁾ and f⁽²⁾ to get final assignment f

**Claim**: This algorithm achieves value at least 1/2 + Ω(1), contradicting the NP-hardness gap.

### 5. The Conclusion

Since the algorithm solves an NP-hard gap problem in polynomial time, Cui concludes P = NP.

## The Error in the Proof

The fundamental error in this proof lies in **invalid application of the Charikar & Wirth algorithm and misunderstanding of the hardness reduction**.

### Critical Flaws:

#### 1. **Invalid Reduction from Tri-linear to Bi-linear Forms**

The paper claims to convert the tri-linear form I⁽³⁾ into a bi-linear form I⁽²⁾ by introducing new variables x⁽²³⁾ᵢ₂ᵢ₃. However:

- **Problem**: The Charikar & Wirth algorithm applies to quadratic programs (bi-linear forms), but the reduction from a 3-XOR instance to a quadratic program is not trivial or automatic
- **Gap**: The paper does not prove that optimizing I⁽²⁾ corresponds to optimizing the original 3-XOR instance
- **Missing proof**: There's no justification that the constraints and structure of the 3-XOR problem are preserved in this transformation

#### 2. **Circular Reasoning in the Algorithm**

The proof claims:
- Step 1 returns f⁽¹⁾ under which I⁽²⁾ ≥ Ω(1) (citing Lemma 5 from [3])
- By "enumeration arguments," there exists f' such that I⁽³⁾ subject to f⁽¹⁾ ≥ Ω(1)
- Step 2 returns f⁽²⁾ achieving this bound

**Flaw**: The "enumeration arguments" are never proven or justified. This is a critical gap because:
- If we need to enumerate all possible assignments to find f', that would take exponential time
- The claim that such an f' exists with the required property is unsubstantiated
- Even if f' exists, finding it efficiently is the core of the problem

#### 3. **Misapplication of Lemma 5 from Charikar & Wirth**

- **Original context**: Lemma 5 in [3] applies to specific quadratic programs with certain structural properties
- **Missing verification**: The paper doesn't verify that the transformed problem I⁽²⁾ satisfies the preconditions of Lemma 5
- **Algorithm mismatch**: Running the SDP algorithm "for two rounds" is not a standard technique and its correctness is never established

#### 4. **Gap Between Soundness and Algorithm Performance**

The paper claims the algorithm achieves value ≥ 1/2 + Ω(1), but:
- **Vague bound**: Ω(1) is not explicitly computed or bounded
- **Comparison error**: Even if the algorithm achieves some constant advantage, this doesn't immediately contradict the hardness result unless ε can be made arbitrarily small while maintaining the Ω(1) advantage
- **Missing analysis**: No rigorous analysis shows the algorithm consistently beats the 1/2 + ε soundness threshold for all ε

#### 5. **Ignoring the Dictatorship Test Structure**

Chan's hardness result relies on a sophisticated dictatorship test composed with Label-Cover:
- The hardness comes from the composition structure
- The paper doesn't address how the SDP algorithm handles this composed structure
- The folding and noise operations in the dictatorship test are not accounted for in the algorithm

#### 6. **Fundamental Misunderstanding of Hardness Results**

- **Key insight**: NP-hardness of approximation doesn't mean no algorithm can achieve better than random performance on *some* instances
- **The error**: The hardness result states it's NP-hard to *distinguish* between high-value and low-value instances
- **What's missing**: Even if an SDP algorithm achieves good value on satisfiable instances, it doesn't resolve the distinguishing problem unless it can also certify when instances have low value

## Formalization Strategy

To formalize this proof attempt and identify the errors, we will:

1. **Define the 3-XOR problem and its gap version**
2. **Formalize Chan's Theorem 1** (the NP-hardness result)
3. **Formalize the Charikar & Wirth SDP algorithm and its guarantees**
4. **Attempt to formalize Cui's reduction** from tri-linear to bi-linear forms
5. **Attempt to formalize Cui's two-round algorithm**
6. **Identify where the formalization fails** (proof obligations that cannot be satisfied)

The formalization will make explicit:
- The missing proof that the reduction preserves problem structure
- The unsubstantiated "enumeration arguments"
- The gap in applying Lemma 5 from [3]
- The invalid conclusion from "algorithm performance" to "P = NP"

## Directory Structure

```
proofs/attempts/peng-cui-2014-peqnp/
├── README.md              (this file)
├── paper.pdf             (the original arXiv paper)
├── coq/
│   └── PengCui2014.v    (Coq formalization)
├── lean/
│   └── PengCui2014.lean (Lean formalization)
└── isabelle/
    └── PengCui2014.thy  (Isabelle formalization)
```

## Key Definitions to Formalize

### 1. Max k-CSP
- Decision problems
- Constraint satisfaction problems
- Value of an assignment

### 2. 3-XOR
- Boolean variables over {1, -1}
- XOR constraints
- Balanced pairwise independent distributions
- Biased distributions

### 3. Gap Problems
- Completeness and soundness parameters
- NP-hardness of distinguishing

### 4. SDP Algorithms
- Semi-definite programming
- Charikar & Wirth algorithm
- Performance guarantees

### 5. The Claimed Algorithm
- Reduction to bi-linear form
- Two-round SDP execution
- Performance analysis

## Expected Formalization Outcomes

For each proof assistant, we expect to:

1. ✅ Successfully formalize the problem definitions
2. ✅ State Chan's Theorem 1 (assume as axiom since it's proven separately)
3. ✅ State the Charikar & Wirth guarantees (assume as axiom)
4. ❌ **Fail to prove** the reduction from I⁽³⁾ to I⁽²⁾ preserves optimality
5. ❌ **Fail to prove** the "enumeration arguments" claim
6. ❌ **Fail to prove** the algorithm runs in polynomial time with the claimed guarantees
7. ❌ **Fail to prove** P = NP from the algorithm's existence

The formalization will reveal precise **proof obligations that cannot be satisfied**, demonstrating where the original proof is invalid.

## References

1. **Peng Cui** (2014). "Approximation Resistance by Disguising Biased Distributions." arXiv:1401.6520v24 [cs.CC]
2. **Chan, S. O.** (2013). "Approximation resistance from pairwise independent subgroups." STOC 2013.
3. **Charikar, M. & Wirth, A.** (2004). "Maximizing quadratic programs: Extending Grothendieck's inequality." FOCS 2004.
4. **Austrin, P., & Mossel, E.** (2009). "Approximation resistant predicates from pairwise independence." Computational Complexity.
5. **Håstad, J.** (2001). "Some optimal inapproximability results." Journal of the ACM.

## Related Work

- [P = NP proofs](../../p_eq_np/) - Framework for testing P = NP claims
- [P ≠ NP proofs](../../p_not_equal_np/) - Framework for testing P ≠ NP claims
- [Barrier results](../../../TOOLS_AND_METHODOLOGIES.md) - Known barriers to P vs NP resolution

## Notes

- The paper went through 24 revisions (v1 through v24), with some versions withdrawn
- The claim remained controversial and was never accepted by the community
- No independent verification or peer-reviewed publication confirmed the result
- The paper demonstrates common pitfalls in complexity theory proofs:
  - Misunderstanding approximation hardness results
  - Unjustified algorithmic claims
  - Missing rigor in reduction arguments

## Status

- 🚧 Coq formalization: In progress
- 🚧 Lean formalization: In progress
- 🚧 Isabelle formalization: In progress
- ⏳ Error identification: Pending formalization completion

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #110](https://github.com/konard/p-vs-np/issues/110)
