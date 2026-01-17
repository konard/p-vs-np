# Formalization: Roman Yampolskiy (2011) - P≠NP

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 77 (from Woeginger's list)
- **Author**: Roman V. Yampolskiy
- **Year**: 2011
- **Claim**: P ≠ NP
- **Paper**: "Construction of an NP Problem with an Exponential Lower Bound"
- **Source**: http://arxiv.org/abs/1111.0305
- **Status**: ❌ **REFUTED** - Contains fundamental errors

---

## Executive Summary

Yampolskiy attempts to prove P ≠ NP by constructing a variant of the Traveling Salesman Problem called the **Hashed-Path Traveling Salesperson Problem (HPTSP)**. The paper claims that HPTSP is in NP but has no polynomial time algorithm because hash functions prevent "pruning" the search space using local information about sub-routes.

**The Fatal Flaw**: The proof confuses *hardness in practice* with *computational complexity theory*. The argument relies on properties of specific hash functions (like SHA-1) which are not formally proven and may not hold. More critically, the paper fails to provide a rigorous proof that HPTSP cannot be solved in polynomial time - it merely argues intuitively that hashing "should" prevent pruning.

---

## The Main Argument

### HPTSP Definition

HPTSP modifies TSP as follows:
1. Start with a standard TSP instance: complete graph G = (V, E) with edge costs
2. For each Hamiltonian cycle (route), encode it as a string including vertices and edge weights
   - Example: route A→B→C→D becomes string "A1B2C3D4" (where 1,2,3,4 are edge weights)
3. Apply a cryptographic hash function h (like SHA-1) to each route string
4. **Question**: Find the route whose hash has the lexicographically smallest value

Formally: `HPTSP = {<G, h, m> : ∃ route z such that h(z) ≤ m lexicographically}`

### Why Yampolskiy Claims HPTSP ∈ NP

**Certificate**: A sequence of |V| vertices with edge costs inserted (e.g., "A1B2C3D4")

**Verification Algorithm**:
1. Check vertices don't repeat and all are included: O(V)
2. Verify edge costs are correct: O(V)
3. Compute hash h(certificate): O(V) (hash function processes input linearly)
4. Check lexicographic ordering: O(V)

**Total**: O(V) polynomial time verification ✓

This part is actually correct - HPTSP is indeed in NP.

### Why Yampolskiy Claims HPTSP ∉ P

The core argument (from pages 6-7 of the paper):

> "In the TSP case, each edge contains information about its length, a value which could be compared to other edges or even full paths to make decisions about pruning. In the case of the HPTSP edge information leaks no information about the value of the total solution... Because the information about local sectors is not sufficient to evaluate the complete path and can't be extracted or evaluated in relation to other sectors, no pruning of paths is possible. This forces any algorithm to consider all possible paths in a search for an optimal solution, requiring an exponential lower bound for HPTSP."

The argument relies on:
1. **Avalanche Effect**: Hash functions like SHA-1 have the property that changing a single bit in the input changes ~50% of output bits
2. **No Local Information**: Therefore, you cannot determine the hash value of a complete path from partial path information
3. **No Pruning Possible**: Without local information, you cannot eliminate paths without examining them
4. **Exponential Lower Bound**: Must examine all V! paths → exponential time

---

## The Critical Errors

### Error 1: Unproven Cryptographic Assumptions

**Problem**: The argument assumes hash functions have certain properties (avalanche effect, computational irreducibility) that are:
- Not mathematically proven
- Not necessary for the complexity-theoretic definition of hash functions
- Potentially breakable (SHA-1 has known collision vulnerabilities)

**Why This Matters**: Computational complexity theory deals with *worst-case guarantees over all inputs*, not average-case behavior of specific functions. Even if SHA-1 behaves randomly in practice, this doesn't constitute a mathematical proof.

**Counterpoint from the Paper** (page 7): "Could someone cryptanalyse the hash function and figure out how hash values are determined? Yes, but to obtain specific hash values a particular input string would need to be analyzed and there is an exponential number of such strings."

**Rebuttal**: This response misses the point. We don't need to "cryptanalyze" individual strings. We need to show there exists *no polynomial-time algorithm* for HPTSP, but the paper only shows specific approaches (based on local information) don't work.

### Error 2: Absence of Rigorous Lower Bound Proof

**Problem**: The paper provides *no formal proof* that HPTSP requires exponential time. It only argues intuitively:
- "Pruning isn't possible" (unproven)
- "Therefore must check all paths" (doesn't follow)
- "Therefore exponential time" (conclusion)

**What's Missing**:
- No reduction from a known hard problem
- No diagonalization argument
- No adversary construction for lower bounds
- No circuit lower bound
- No communication complexity argument

**Standard of Proof**: To prove a problem is not in P, you must show that *every possible polynomial-time algorithm fails*. Yampolskiy only shows that certain *intuitive approaches* fail.

### Error 3: Conflation of "No Pruning" with "Exponential Time"

**Problem**: Even if hashing prevents pruning based on local information, this doesn't prove exponential time is required.

**Why**: There might be:
- Clever algorithms that work directly on the problem structure
- Randomized algorithms
- Algorithms that exploit the specific construction
- Algebraic or number-theoretic approaches

**Example**: Consider sorting. You can't "prune" comparisons in an adversarial setting, but sorting still has O(n log n) algorithms (not exponential!). The absence of obvious pruning doesn't imply exponential complexity.

### Error 4: The "Random String Compression" Argument is Flawed

From page 7:

> "Suppose that the edge costs of an HPTSP instance are randomly generated... An ability to compute the full lexicographic order of an encoded path without examining all of it would essentially be the same as being able to compress a string of random numbers which is a contradiction."

**Problems**:
1. **Not all HPTSP instances have random edge costs** - the problem definition doesn't require this
2. **Incompressibility of random strings** is an information-theoretic property, not a computational one
3. **You can compute properties of incompressible strings** in polynomial time (e.g., "does this string contain more 0s than 1s?")

### Error 5: Incorrect Understanding of Complexity Classes

**Critical Quote** (page 9):

> "Either P is not equal to NP or it is possible to prune most HPTSP paths without examining them."

This is a **false dichotomy**. The correct statement would be:

> "Either P is not equal to NP or there exists a polynomial-time algorithm for HPTSP."

The algorithm might not work by "pruning" at all! It might:
- Use dynamic programming
- Exploit mathematical structure
- Use clever data structures
- Apply transformations we haven't thought of

### Error 6: Circular Reasoning About NP-Intermediate

**Paper's Conclusion** (page 1):

> "As a consequence, via Ladner's theorem, we show that the class NPI is non-empty."

**Ladner's Theorem** (1975): *If P ≠ NP*, then there exist NP-intermediate problems.

**The Circularity**:
1. Paper assumes it proved HPTSP ∈ NP but HPTSP ∉ P
2. Paper assumes HPTSP is not NP-complete (not proven!)
3. Paper concludes P ≠ NP (from HPTSP ∉ P)
4. Paper then uses Ladner's theorem to claim NPI is non-empty

**The Problem**: You can't use Ladner's theorem to prove P ≠ NP - it *assumes* P ≠ NP! This is backwards.

---

## What Yampolskiy Actually Showed

To be fair, the paper does demonstrate something interesting (though not groundbreaking):

✅ **HPTSP is a well-defined problem in NP**
✅ **HPTSP is "hard to solve with obvious approaches"** (heuristics, local search)
✅ **Hash functions can be used to construct artificial hard-looking problems**
❌ **HPTSP is not in P** (NOT proven)
❌ **P ≠ NP** (NOT proven)

---

## The Proof-Theoretic Challenge

Our formalization attempts to encode Yampolskiy's argument in three proof assistants (Coq, Lean, Isabelle) with the following goals:

1. **Formalize HPTSP**: Define the problem precisely
2. **Prove HPTSP ∈ NP**: Encode the verification algorithm
3. **Attempt to prove HPTSP ∉ P**: This is where we expect the formalization to fail or require unjustified axioms
4. **Identify the exact gap**: Pinpoint which step cannot be completed in a proof assistant

The formalization will make explicit what the paper leaves implicit: the logical gap between "intuitive hardness" and "proven complexity lower bound."

---

## Formalizations

### Coq Implementation
- **File**: `coq/YampolskiyHPTSP.v`
- **Status**: Defines HPTSP, proves membership in NP, axiomatizes unproven claims about hash functions
- **Key Gap**: Cannot prove `HPTSP_not_in_P` without additional axioms

### Lean Implementation
- **File**: `lean/YampolskiyHPTSP.lean`
- **Status**: Uses dependent types to encode the problem, marks non-constructive proofs with `sorry`
- **Key Gap**: The statement "no pruning is possible" cannot be formalized rigorously

### Isabelle/HOL Implementation
- **File**: `isabelle/YampolskiyHPTSP.thy`
- **Status**: Higher-order logic formalization, uses `oops` to mark incomplete proofs
- **Key Gap**: The leap from "hash functions hide information" to "exponential lower bound" is not derivable

---

## Related Work and Context

### Similar Failed Attempts

Yampolskiy's approach is similar to other failed attempts that try to:
1. Construct an "obviously hard" problem
2. Argue informally about its difficulty
3. Claim this proves P ≠ NP

**Why These Fail**: Complexity theory has high standards for lower bound proofs. Intuition is not enough.

### Known Barriers to P ≠ NP Proofs

Any valid P ≠ NP proof must overcome:

1. **Relativization Barrier** (Baker-Gill-Solovay, 1975): Techniques that relativize cannot separate P from NP
2. **Natural Proofs Barrier** (Razborov-Rudich, 1997): Proofs that work by finding "natural" properties of Boolean functions are unlikely to work
3. **Algebrization Barrier** (Aaronson-Wigderson, 2008): Extension of relativization

**Does Yampolskiy's Approach Overcome These?**
❌ No. The argument would relativize (adding an oracle doesn't help), so it cannot work.

---

## Educational Value

Despite being incorrect, this paper is valuable for teaching because it:

1. **Shows a common mistake**: Confusing "hard in practice" with "provably hard"
2. **Illustrates the gap** between intuition and proof
3. **Demonstrates why formal verification matters**: A proof assistant would immediately flag the gaps
4. **Provides a concrete example** of why P vs NP is still open

---

## References

### Primary Source
- Yampolskiy, R. V. (2011). "Construction of an NP Problem with an Exponential Lower Bound." arXiv:1111.0305.

### Complexity Theory Background
- Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach.* Cambridge University Press.
- Sipser, M. (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.

### Barrier Results
- Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P =? NP Question." *SIAM Journal on Computing*, 4(4), 431-442.
- Razborov, A. A., & Rudich, S. (1997). "Natural Proofs." *Journal of Computer and System Sciences*, 55(1), 24-35.
- Aaronson, S., & Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory." *STOC 2008*.

### Hash Functions and Cryptography
- Wang, X., Yin, Y. L., & Yu, H. (2005). "Finding Collisions in the Full SHA-1." *CRYPTO 2005*. (Shows SHA-1 vulnerabilities)

### Woeginger's List
- Woeginger, G. J. "The P-versus-NP page." https://www.win.tue.nl/~gwoegi/P-versus-NP.htm

---

## Verification Status

| Proof Assistant | Definition Complete | NP Membership Proven | P Non-Membership Attempted | Gap Identified |
|----------------|---------------------|---------------------|----------------------------|----------------|
| Coq            | ✅                  | ✅                  | ⚠️ (requires axioms)       | ✅             |
| Lean           | ✅                  | ✅                  | ⚠️ (uses sorry)            | ✅             |
| Isabelle/HOL   | ✅                  | ✅                  | ⚠️ (uses oops)             | ✅             |

---

## Conclusion

Yampolskiy's HPTSP paper is a well-intentioned but ultimately unsuccessful attempt to prove P ≠ NP. The core issue is the lack of a rigorous proof that HPTSP requires exponential time. While the intuition about hash functions "hiding information" is appealing, it does not constitute a complexity-theoretic lower bound proof.

**The Key Lesson**: In complexity theory, we must distinguish between:
- **Hard in practice** (no known efficient algorithms)
- **Provably hard** (proven that no efficient algorithm exists)

HPTSP may be the former, but the paper does not establish the latter.

Our formal verification exercise makes this gap explicit and provides a concrete example of why formal methods are valuable in mathematical research.

---

**Last Updated**: 2025-10-26
**Formalization by**: AI Issue Solver (Issue #54)
