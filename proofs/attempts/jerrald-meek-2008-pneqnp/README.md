# Jerrald Meek (2008) - P≠NP Attempt

**Attempt ID**: 43
**Author**: Jerrald Meek
**Year**: April 2008 (final revision September 2008)
**Claim**: P ≠ NP
**Paper**: "P is a proper subset of NP"
**Source**: [arXiv:0804.1079](https://arxiv.org/abs/0804.1079)
**Listed on**: [Woeginger's P versus NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #43)

## Summary

Jerrald Meek attempts to prove P ≠ NP by analyzing the **computational rate** of polynomial-time algorithms on NP-complete problems. The author argues that as the number of clauses in an NP-complete problem approaches infinity, the number of input sets processed per computation also approaches infinity, leading to the conclusion that any polynomial-time solution must examine only a polynomial subset of inputs, which the author claims is impossible to find efficiently.

### Main Claim

> "As the number of clauses in a NP-complete problem approaches infinity, the number of input sets processed per computations performed also approaches infinity when solved by a polynomial time solution."

In other words, Meek claims that:
1. NP-complete problems have **exponentially many** possible input sets (2^(kn) for k-SAT)
2. A polynomial-time algorithm can only perform **polynomially many** computations
3. Therefore, the ratio of input sets to computations approaches infinity
4. This implies any P=NP algorithm must find a "representative polynomial search partition" in polynomial time
5. Finding such a partition is itself an **FEXP-hard** problem (exponential time)
6. Therefore, P ≠ NP

## The Argument

### Core Approach

Meek's argument proceeds through several key theorems:

1. **Computational Rate Analysis** (Section 3.2):
   - For k-SAT with n clauses, there are 2^(kn) possible input sets
   - A polynomial-time solution performs t(n) = O(n^p) computations
   - The "rate" r(n) = 2^(kn) / t(n) represents input sets processed per computation
   - As n → ∞, this rate r(n) → ∞

2. **P = NP Optimization Theorem** (Theorem 4.4):
   - "The only deterministic optimization of a NP-complete problem that could prove P = NP would be one that can always solve a NP-complete problem by examining no more than a polynomial number of input sets for that problem."

3. **P = NP Search Partition Theorem** (Theorem 5.1):
   - "The only deterministic search optimization of a NP-complete problem that could prove P = NP would be one that can always find a representative polynomial search partition by examining no more than a polynomial number of input sets from the set of all possible input sets."

4. **The Circular Trap** (Section 6):
   - To find a polynomial search partition in polynomial time, you need another polynomial search partition
   - This creates a circular dependency: you need a polynomial-time algorithm to find the partition that would enable the polynomial-time algorithm

### Key Mathematical Claims

1. Using L'Hôpital's rule to show exponential functions dominate polynomial functions
2. Proving lim(n→∞) 2^(kn)/t(n) = ∞ for polynomial t(n)
3. Arguing that finding a "representative polynomial search partition" by exhaustion requires exponential time (FEXP)
4. Concluding that since partition-finding is exponential, P ≠ NP

## The Error

### Critical Flaw: Confusing Search Space with Computation

The fundamental error in Meek's attempt is a **confusion between the number of possible inputs and the number of computations required to solve a problem**. This manifests in several critical ways:

### 1. **Incorrect Model of Polynomial-Time Algorithms**

Meek assumes that solving an NP problem requires "processing" all possible input sets:

> **Error**: The claim that r(n) = 2^(kn)/t(n) represents "input sets processed per computation" is **fundamentally flawed**.

A polynomial-time algorithm for SAT (if one exists) would not "process input sets" - it would directly compute whether a given formula is satisfiable. The 2^(kn) possible truth assignments are not "inputs" to the algorithm; they are the **search space** that a naive algorithm might explore, but a clever algorithm could avoid.

**Analogy**: This is like claiming you cannot find a specific book in a library of 2^n books in polynomial time because you'd need to examine all 2^n books. But with a proper indexing system (algorithm), you can find it in O(log n) time.

### 2. **The "Search Partition" Is Not Required**

Meek's central claim that P=NP algorithms must find a "representative polynomial search partition" is **unsupported**:

- **False Premise**: There is no requirement that a polynomial-time algorithm for SAT must explicitly enumerate a subset of satisfying assignments
- **Misunderstanding**: A decision algorithm only needs to determine IF a solution exists, not FIND a representative subset of all solutions
- **Counterexample**: Consider polynomial-time solvable problems like 2-SAT - these don't work by finding "search partitions"; they use algorithmic techniques like unit propagation and implication graphs

### 3. **Circular Reasoning Through Unfounded Assumptions**

The "P = NP Optimization Theorem" (Theorem 4.4) is presented as proven, but it actually **assumes what it claims to prove**:

```
Meek's Logic:
1. Assume any P=NP algorithm must examine ≤ poly(n) input sets [UNPROVEN]
2. There are 2^(kn) total input sets
3. Finding which poly(n) sets to examine is hard [CIRCULAR]
4. Therefore P ≠ NP [INVALID]
```

**The Gap**: Step 1 is never rigorously justified. Meek argues that since r(n) → ∞, the algorithm "must" examine fewer sets, but this doesn't follow. A polynomial-time algorithm might:
- Use algebraic or logical manipulations (not search)
- Exploit problem structure in ways that don't involve enumerating assignments
- Transform the problem into a different representation entirely

### 4. **Misapplication of Asymptotic Analysis**

The limit lim(n→∞) 2^(kn)/t(n) = ∞ is **mathematically correct** but **computationally irrelevant**:

- **Correct**: Exponential functions grow faster than polynomials
- **Irrelevant**: This says nothing about whether a problem can be solved in polynomial time
- **Non-sequitur**: The ratio approaching infinity doesn't imply anything about computational complexity

**Example**: Consider sorting n numbers. There are n! possible permutations (exponential in n), but we can sort in O(n log n) time. The ratio (n!)/(n log n) → ∞, but this doesn't prove sorting requires exponential time.

### 5. **The FEXP Partition-Finding Claim Is Unjustified**

Meek claims (Section 5.1.2) that finding a "representative polynomial search partition" is FEXP-hard:

**Error**: This argument assumes:
1. The partition must be found by exhaustive search over all 2^(kn) assignments
2. There's no structure that allows efficient partition identification

But this is **circular**: If P=NP, then by definition, there exists a polynomial-time algorithm that doesn't require exhaustive search. Meek is assuming P≠NP (that no efficient method exists) to prove P≠NP.

### 6. **Confusing NP Membership with Hardness**

Throughout the paper, Meek conflates:
- **NP** (problems with polynomial-time verifiable solutions)
- **NP-complete** (hardest problems in NP)
- **Exponential-time solvability** (current best algorithms)

The fact that we currently solve SAT using exponential-time algorithms doesn't mean polynomial-time algorithms are impossible - it means we haven't found them yet (or they don't exist, but that's what needs to be proven, not assumed).

### 7. **The Dependency on Unpublished/Rejected Articles**

Meek's conclusion relies on claims from three other papers in his series:
- Article 2: "Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem"
- Article 3: "Independence of P vs. NP in regards to oracle relativizations"
- Article 4: "Analysis of the postulates produced by Karp's Theorem"

The conclusion states:
> "(3) Some NP-complete problems can only have a deterministic polynomial time solution if the SAT problem has a deterministic polynomial time solution.
> (4) SAT does not have a deterministic polynomial time solution."

**Critical Issue**: These claims are asserted but not proven within this paper, and the referenced articles show similar flaws. This creates a circular dependency where unproven claims support each other.

## Why This Approach Cannot Work

### Barrier Analysis

Meek's approach fails to address known barriers to proving P ≠ NP:

1. **Relativization** (Baker-Gill-Solovay, 1975): There exist oracles relative to which P=NP and oracles relative to which P≠NP. Any proof that "relativizes" (works the same with oracle access) cannot resolve P vs NP. Meek's counting argument would relativize, so it cannot be valid.

2. **Natural Proofs** (Razborov-Rudich, 1997): Meek's argument attempts to show a "natural property" that distinguishes P from NP-complete problems, but doesn't address why this doesn't fall into the natural proofs barrier.

3. **Algebrization** (Aaronson-Wigderson, 2008): Modern barrier that Meek's 2008 paper could not have addressed, but which would likely apply to this type of argument.

### What's Actually Being Measured

When Meek computes r(n) = 2^(kn)/t(n), he's measuring:
- **Numerator**: The size of the solution space (exponential)
- **Denominator**: Hypothetical running time (polynomial)

This ratio tells us **nothing** about:
- Whether the problem can be solved without enumerating the space
- Whether structure exists that allows efficient solving
- Whether P = NP or P ≠ NP

### The Core Misunderstanding

**Meek's implicit assumption**: Solving SAT = Searching through assignments

**Reality**: Solving SAT might involve:
- Algebraic transformations
- Structural decomposition
- Novel algorithmic techniques we haven't discovered
- Exploiting hidden structure in the problem

The entire argument rests on the assumption that any algorithm must essentially "touch" or "process" a large number of possible assignments, but this is **exactly the assumption that P≠NP makes**. Using it to prove P≠NP is circular.

## Formalization Approach

Our formalization attempts to:

1. **Formalize** the core claims about computational rates and search partitions
2. **Identify** where the informal reasoning breaks down
3. **Demonstrate** that the key theorems either:
   - Are trivially true (2^n > n^k for large n) but don't imply P≠NP
   - Assume P≠NP in their premises (circular reasoning)
   - Make unjustified leaps from counting arguments to complexity results

## Formalization Status

### Lean (`lean/MeekAttempt.lean`)
- Models computational complexity classes (P, NP, NP-complete)
- Formalizes the "computational rate" concept
- **Identifies the gap**: The ratio r(n) → ∞ doesn't imply partition-finding is hard
- **Shows circularity**: "Search partition theorem" assumes P≠NP

### Coq (`coq/MeekAttempt.v`)
- Provides formal definitions of the key claims
- **Identifies the gap**: No proof that algorithms must "process" input sets
- **Shows invalid inference**: Asymptotic ratio doesn't determine complexity

### Isabelle (`isabelle/MeekAttempt.thy`)
- Structured representation of the argument
- **Identifies the gap**: The FEXP claim is circular
- **Shows dependency issues**: Relies on unproven claims from other papers

## Conclusion

Meek's attempt is **not a valid proof** of P ≠ NP because:

1. ❌ **Confuses search space with computational requirements** - assumes algorithms must enumerate assignments
2. ❌ **Circular reasoning** - assumes P≠NP (no efficient partition-finding) to prove P≠NP
3. ❌ **Unjustified "search partition" requirement** - no proof that algorithms must work this way
4. ❌ **Invalid inference from asymptotic analysis** - ratio approaching infinity doesn't imply hardness
5. ❌ **Depends on unproven claims** in other (rejected) papers in the series
6. ❌ **Doesn't address known barriers** - would likely fail relativization
7. ❌ **Misunderstands polynomial-time algorithms** - they don't work by "processing input sets"

### What This Shows

This formalization demonstrates an important lesson: **Counting arguments about solution spaces do not directly translate to computational complexity results**. The size of the search space (exponential) and the running time of the best algorithm (polynomial, exponential, or otherwise) are related but distinct concepts. A valid proof of P ≠ NP must show that **every possible algorithm** requires superpolynomial time, not just that naive enumeration does.

### Historical Context

This paper received feedback from Stephen Cook (who is acknowledged in the paper), went through 12 revisions, but was never accepted for publication. The author noted that Cook "identified an incorrect premise in a previous version of this article which was related to the nature of non determinism," leading to a major revision. However, the fundamental conceptual errors remained in the final version.

## References

1. Meek, J. (2008). "P is a proper subset of NP", arXiv:0804.1079v12
2. Woeginger, G. J. "The P-versus-NP page", https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. Cook, S. A. (1971). "The complexity of theorem-proving procedures", STOC 1971
4. Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P=?NP Question", SIAM Journal on Computing
5. Razborov, A., Rudich, S. (1997). "Natural Proofs", Journal of Computer and System Sciences
6. Aaronson, S., Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory", STOC 2008

## Related Work

- [proofs/p_not_equal_np/](../../p_not_equal_np/README.md) - Framework for verifying P ≠ NP proof attempts
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](../../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Catalog of valid approaches
- [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md) - Tools for formal verification
