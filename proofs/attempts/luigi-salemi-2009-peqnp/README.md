# Luigi Salemi (2009) - P=NP Proof Attempt

**Attempt ID**: 57 (Woeginger's list)
**Author**: Luigi Salemi
**Year**: 2009
**Claim**: P = NP
**arXiv**: [0909.3868v2](http://arxiv.org/abs/0909.3868)
**Status**: **Refuted** - Contains critical errors in the proof strategy

## Summary

In September 2009, Luigi Salemi submitted a paper titled "Method of resolution of 3SAT in polynomial time" claiming to prove P = NP by providing a polynomial-time algorithm for solving 3SAT with runtime O(n^15). The paper presents an elaborate method involving transformations of 3SAT instances and operations called "Reduction" and "Saturation" that allegedly preserve solutions while determining satisfiability in polynomial time.

## Main Approach

Salemi's approach involves transforming a 3SAT problem into a complementary representation and then applying operations to determine satisfiability:

### 1. Core Transformation: CI3Sat

**CI3Sat** (Complementation of Inverse 3SAT) is constructed as follows:
- Given a 3SAT formula with n variables
- Create n*(n-1)*(n-2)/6 "Rows," one for each triple (Ai, Aj, Ak) of variables
- Each Row contains "AClausolas" (conjunctions of 3 literals)
- An AClausola (Li AND Lj AND Lk) is in a Row if the corresponding Clause (Li OR Lj OR Lk) is NOT in the original 3SAT

**Key Claim**: 3SAT has a solution if and only if CI3Sat has a solution (Theorem 3)

### 2. The "Reduction" Operation

The Reduction operation aims to simplify CI3Sat without losing solutions:

1. Find a pair of literals (Li, Lj) that is **absent** from some Row
2. Remove all AClausolas containing this pair from **all** Rows
3. Repeat until no more pairs can be eliminated or a Row becomes empty

**Claimed Complexity**: O(n^9)
**Claimed Property**: Reduction never decreases the number of solutions (Theorem 6)

### 3. The "Saturation" Operation

Saturation is the most complex operation:

For each AClausola (Li AND Lj AND Lk) in CI3Sat:
1. Create a test copy: Apply Imposition Li, Imposition Lj, Imposition Lk (eliminating AClausolas with ~Li, ~Lj, ~Lk)
2. Apply Reduction to the test copy
3. If the test Reduction makes CI3Sat empty, delete this AClausola from the original CI3Sat and apply Reduction
4. Otherwise, discard the test and continue to the next AClausola
5. Repeat until CI3Sat is empty or no more AClausolas can be deleted

**Claimed Complexity**: O(n^15)
**Claimed Property**: Saturation never decreases solutions (Theorem 8)

### 4. The Main Theorem

**Theorem 11 & 12**: CI3Sat Saturated has a solution if and only if it is not empty.

The paper claims to provide a constructive proof by building a consistent assignment of truth values when CI3Sat Saturated is non-empty.

### 5. The P=NP Conclusion

By combining these results, Salemi claims:
- We can determine if 3SAT has a solution in O(n^15) time
- Since 3SAT is NP-complete, this implies P = NP

## The Critical Errors

### Error 1: Incorrect Complexity Analysis of Saturation

The **most severe error** is in the complexity analysis of the Saturation operation.

**The Problem**: Salemi claims Saturation runs in O(n^15) time, but this analysis is fundamentally flawed:

1. **Iteration Count Underestimate**: Salemi assumes Saturation requires at most O(n^3) iterations (one per AClausola). However:
   - The number of iterations depends on how many AClausolas are deleted
   - Deleting one AClausola may enable deletion of others that couldn't be deleted before
   - In the worst case, the **order** in which AClausolas are tested matters critically
   - No proof is given that O(n^3) iterations suffice

2. **Missing Dependency Analysis**: Each iteration involves:
   - Testing an AClausola by imposing 3 literals and reducing: O(n^9)
   - But which AClausolas can be deleted depends on **the state after previous deletions**
   - This creates a complex dependency structure that isn't analyzed

3. **Actual Complexity**: The Saturation operation as described has worst-case complexity **at least O(n^3 × n^9) = O(n^12)** per outer iteration, but:
   - The number of outer iterations could be exponential in n
   - No termination bound is proven beyond "until nothing changes"
   - The operation could easily require exponentially many iterations

**Why This Matters**: Without a polynomial bound on iterations, the entire algorithm is not proven polynomial-time.

### Error 2: Circular Logic in Theorem 11 (Constructive Proof)

The proof of Theorem 11 claims to construct a solution for non-empty saturated CI3Sat by making "Consistent Choices."

**The Fatal Flaw**:

1. The proof assumes that after choosing literals A1, A2, A3, ... Ak-1, we can always choose Ak such that all required AClausolas exist
2. The argument for why AClausola (A5 AND A6 AND A7) must exist (pages 7-8) is **proof by contradiction**:
   - Assumes it's missing
   - Claims this would make CI3Sat(4) empty after Reduction
   - Concludes it cannot be missing because CI3Sat is saturated

3. **The Circularity**: This argument assumes that Saturation **always produces a structure where the construction works**
4. But Saturation's correctness depends on Theorem 11 being true
5. And Theorem 11's proof depends on properties that Saturation is assumed to guarantee

**The Real Issue**: The proof doesn't establish that Saturation actually achieves the properties needed for the construction to work. It assumes these properties hold because "CI3Sat is Saturated," but never proves that Saturation guarantees them.

### Error 3: Theorem 7 Does Not Support the Claims

Theorem 7 states: "After Reduction, if a Row has a Literal, then any Row with the Variables of that Literal has the same Literal."

**The Problem**:
1. This theorem is used crucially in the proof that the construction works
2. But the proof of Theorem 7 itself has gaps
3. The "absurd" argument assumes Reduction has already eliminated all problematic cases
4. No proof is given that Reduction necessarily achieves this property in polynomial time

**Missing**: A proof that Reduction can detect and eliminate all violations of this property without exponential backtracking.

### Error 4: The "Coincidence" Is Not Explained

Salemi notes a "coincidence" that the number of AClausolas in saturated CI3Sat equals the number of distinct triples of TRUE values across all solutions (Corollary 11.6).

**The Problem**:
1. This is presented as a **consequence** of the construction, but it's actually **required** for the construction to work
2. If this property doesn't hold, the constructive proof of Theorem 11 fails
3. No independent verification is provided that Saturation guarantees this property
4. The claim "WAS NOT A COINCIDENCE!" (page 10) is asserted without rigorous proof

**Why This Matters**: This "coincidence" is actually a strong structural requirement. If Saturation doesn't guarantee it, the entire proof strategy collapses.

### Error 5: No Proof of Correctness for the Construction Algorithm

The constructive proof in Theorem 11 (pages 6-9) has multiple issues:

1. **Variable Reordering**: The proof suggests reordering variables and swapping literals "for simplification"
   - No proof that this reordering is always possible
   - No proof that it can be done in polynomial time
   - No proof that it preserves the solution existence

2. **Choice Ambiguity**: When choosing Ak from Row (Ai, Aj, Ak), the proof gives a procedure (steps a-d on page 7)
   - If multiple Rows have only one literal for Ak, which one to choose?
   - No proof that all valid choices lead to a solution
   - No proof that the procedure terminates in polynomial time

3. **Proof by Cases Is Incomplete**: The proof shows Consistency for A4, A5, A6, A7, A8 and claims "Similar for A9, A10, .., An"
   - But each case requires increasingly complex arguments
   - The pattern doesn't scale uniformly
   - No inductive proof is provided

## Why The Approach Cannot Work

The fundamental issue is that Salemi's approach tries to solve 3SAT by:
1. Creating an exponentially-sized structure (CI3Sat with O(n^3) rows, each potentially having O(1) AClausolas)
2. Iteratively simplifying it with operations whose termination is not bounded
3. Claiming this process is polynomial-time based on **incorrect complexity analysis**

**Key Insight**: The Saturation operation is essentially searching for a maximal consistent subset of AClausolas. This is itself an NP-complete problem (maximal independent set variant). The paper doesn't prove that its specific search strategy runs in polynomial time.

## Related Concepts

- **3SAT**: Boolean satisfiability problem with clauses of exactly 3 literals
- **NP-Completeness**: 3SAT is one of Karp's 21 NP-complete problems
- **Complementation**: Converting clauses to "AClausolas" and vice versa
- **Polynomial Time**: The paper claims O(n^15) but doesn't prove it rigorously
- **Constructive Existence Proofs**: Theorem 11's approach, which has critical gaps

## Formalization Goals

Our formalization aims to:

1. **Formalize the CI3Sat construction** and prove Theorems 1-3 (these are likely correct)
2. **Formalize the Reduction operation** and identify where Theorem 6's proof is incomplete
3. **Formalize the Saturation operation** and show that its complexity is not bounded to O(n^15)
4. **Identify the circularity** in Theorem 11's proof strategy
5. **Show the construction algorithm** in Theorem 11 has cases where it fails or requires exponential time
6. **Demonstrate the gap** between what Saturation achieves and what Theorem 11 requires

## Key Definitions to Formalize

- 3SAT formulas and their solutions
- CI3Sat transformation
- Rows and AClausolas
- Imposition operation
- Reduction operation and its termination
- Saturation operation and its complexity
- The "Consistent Choice" construction
- Group Clause of Solutions (GCS)

## Educational Value

This attempt is valuable for understanding:
- How subtle complexity analysis errors can invalidate P=NP proofs
- Why constructive proofs need rigorous termination arguments
- The danger of circular reasoning in existence proofs
- How operations that "seem polynomial" may have exponential worst-case behavior

## References

- **Original Paper**: Salemi, L. "Method of resolution of 3SAT in polynomial time" (2009)
  - arXiv: [0909.3868](https://arxiv.org/abs/0909.3868)
  - Latest version: v2 (13 Sep 2010), 77 KB

- **Woeginger's List**: Entry #57 at [https://wscor.win.tue.nl/woeginger/P-versus-NP.htm](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

- **3SAT Background**:
  - Cook, S. "The P versus NP Problem" - Clay Mathematics Institute
  - Karp, R. M. (1972) "Reducibility Among Combinatorial Problems"

## Notes

- The paper went through 2 versions (Sep 2009, Sep 2010)
- No withdrawal notice has been posted
- The author's website (http://www.visainformatica.it/3sat) is no longer accessible
- The paper is written in English by a non-native speaker (as acknowledged in the abstract)
