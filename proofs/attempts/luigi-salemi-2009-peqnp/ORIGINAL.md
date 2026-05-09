# Method of resolution of 3SAT in polynomial time

**Author**: Luigi Salemi  
**Date**: September 2010  
**Source**: arXiv:0909.3868v2

## Abstract

Presentation of a Method for determining whether a problem 3Sat has solution, and if yes to find
one, in time max O(n^15). Is thus proved that the problem 3Sat is fully resolved in polynomial time
and therefore that it is in P, by the work of Cook and Levin, and can transform a SAT problem in a
3Sat in polynomial time (ref. Karp), it follows that P = NP.

**Note**: The author acknowledges that "My English is bad, so this work is essential. I hope my page is enough clear"

## Introduction

### Intuition

3Sat problem is research of True Value that making TRUE all Clauses of problem. With n
Variables we find 8n*(n-1)*(n-2)/6 Clauses, this Clauses are not all in 3Sat [max 7/8 are in 3Sat].
We post in ~3Sat Clauses that not is in 3Sat. We move one Clauses from ~3Sat to 3Sat, if number
of solutions not decrease we leave Clause in 3Sat else no. We end if not is possible move Clause
from ~3Sat to 3Sat because we lost solutions. Now we can find one solution, n-tuple of Literal.
This the intuition: minimize Clauses in ~3Sat.

### Coincidence

One operation move, in polynomial time, Clauses from ~3Sat to 3Sat. When it end we
have in ~3Sat Clauses and in all solution triad of True Value. This the coincidence: number of
Clauses in ~3Sat is equal number of tried of True Values, also when we not have Clauses
because not have tried [not have solution]. Really funny, and I not believe in coincidence.

## Definitions

- **Variables**: A1, A2, .., An are n Boolean Variables
- **Negation**: ~A1, ~A2, .., ~An are their negations
- **Values**: Each Variable can have value "TRUE" (T) or "FALSE" (F)
- **Literals**: L1, L2, .., Ln where each Li = Ai or Li = ~Ai
- **Pair of Literal (Li, Lj)**: Set of 2 literals Li, Lj with i < j
  - There are 2n*(n-1) possible Pairs
- **Clause**: Disjunction of 3 Literal [ex.: (Li or Lj or Lk)]
  - Clause is TRUE if at least one Literal is TRUE
  - "Described Sorted" if i < j < k
- **AClausola**: Conjunction of 3 Literal [ex.: (Li and Lj and Lk)]
  - AClausola is TRUE if all Literals are TRUE
  - "Described Sorted" if i < j < k
  - Sometimes written as [Li Lj Lk]
- **Tried of Variables (Ai, Aj, Ak)**: Set of 3 Variables with i < j < k
  - One Tried has 8 Clauses "Described Sorted" and 8 AClausolas "Described Sorted"
  - There are n*(n-1)*(n-2)/6 possible Trieds
- **Row of Variables (Ai, Aj, Ak)**: Set of 0 or more AClausolas "Described Sorted" all of one Tried
  - Max number of AClausolas per Row is 8
  - Max number of Rows is n*(n-1)*(n-2)/6 (one per Tried)
  - If Row contains 0 AClausolas it's called "empty Row"

## The Method

### I3Sat (Inverse 3Sat)

**Definition**: Set of Clauses obtained by substituting any Variables with its negation (then any negation is substituted with Variable).

**Time complexity**: O(n^3)

**Theorem 1**: 3Sat has solution IFF I3Sat has solution, and any solution of one is solution of the other with substitution T with F and F with T.

### C3Sat (Complementation 3Sat)

**Definition**: Set of n*(n-1)*(n-2)/6 ordered Rows, one for any Tried, where any Row has complementary AClausolas [AClausola (Li and Lj and Lk) is in Row if Clause (Li or Lj or Lk) is NOT in 3Sat].

**Time complexity**: O(n^3)

**Solution**: n-tuple of True Values V1, V2, .., Vn solves C3Sat if it makes TRUE one AClausola in any Row.

**Theorem 2**: 3Sat has solution IFF C3Sat has solutions. From any solution of one we make solution of other by simple exchange T with F and F with T.

### CI3Sat (Complementation of Inverse of 3Sat)

**Definition**: Complementation of reverse of 3Sat

**Time complexity**: O(n^3) (create I3Sat and C3Sat, but O(n^3) + O(n^3) = O(n^3))

**Theorem 3**: 3Sat has solution IFF CI3Sat has solution, and any solution of one is solution of the other.

### Operations on CI3Sat

#### Imposition Li

**Definition**: Elimination, in CI3Sat, of all AClausolas with Literal ~Li. Then we leave, if they are, only solutions where Li = TRUE.

**Time complexity**: O(n^3)

**Theorem 4**: Imposition Ai does not decrease and does not increase number of solutions of CI3Sat where Vi = TRUE.

**Theorem 5**: If Imposition Ai makes empty one or more Rows then we have no solution of CI3Sat with Vi = TRUE.

#### Reduction

**Definition**: Find Pair of Literal (Li, Lj) absent in one Row and then remove all AClausolas with this Pair in any Rows of CI3Sat.

**Rationale**: Any Pair of Literal (Li, Lj) absent in Row limits number of solutions - any n-tuple of True Values that makes TRUE formula (Li and Lj) is not solution of CI3Sat. Then any AClausola with Pair (Li, Lj) absent in other Row can be removed from CI3Sat, this does not decrease solutions.

**Time complexity**: O(n^9) - finds Pair in any Row [O(n^3)] and for each finds AClausolas with this Pair in all Rows [O(n^3)]. If not ended, makes new research many times equal to number of AClausolas [O(n^3)].

**Termination**: Ends when:
- Case 1) At least one Row is empty
- Case 2) Reduction does not remove more AClausolas

**Theorem 6**: Reduction does not decrease and does not increase number of solutions of CI3Sat.

**Theorem 7**: After Reduction, if Row has Literal then any Row with Variables of that Literal has same Literal.

#### Saturation

**Definition**: This operation:
1. Extract all AClausolas (Li and Lj and Lk) of CI3Sat
2. For each AClausola:
   - Execute Imposition Li, Imposition Lj, Imposition Lk
   - Execute Reduction
   - If CI3Sat becomes empty: remove this AClausola from original CI3Sat and execute Reduction on original
   - Otherwise: discard test and continue to next AClausola
3. End if CI3Sat is empty or no more AClausolas can be deleted

**Claimed time complexity**: O(n^15) - O(n^3) AClausolas tested, each test requires 3 Impositions [O(n^3)] and Reduction [O(n^9)]

**Theorem 8**: Saturation does not decrease and does not increase number of solutions of CI3Sat.

### Main Theorems

**Theorem 11**: CI3Sat Saturated has solution if and only if it is not empty.

The proof provides a constructive algorithm:
1. Reorder variables if needed
2. Choose literals A1, A2, A3 from appropriate Rows
3. For each subsequent Ak (k from 4 to n), choose from Row (Ai, Aj, Ak) where i < j < k
4. Verify consistency using properties guaranteed by Saturation

**Theorem 12**: CI3Sat Saturated has solution IFF it is not empty.

**P=NP Conclusion**: Since we can determine if 3Sat has solution in O(n^15) time (create CI3Sat in O(n^3), Saturation in O(n^15)), and 3Sat is NP-complete, this implies P = NP.

## Group Clause of Solutions (GCS)

**Definition**: Extract from all solutions of CI3Sat all distinct Tried of True Values.

**Corollary 11.6**: Number of AClausolas in CI3Sat Saturated equals number of distinct Tried of True Values across all solutions.

"WAS NOT A COINCIDENCE!" - This equality is presented as a fundamental structural property.

## Notes

- The paper went through 2 versions (Sep 2009, Sep 2010)
- Open Source program was claimed to be available at http://www.visainformatica.it/3sat (no longer accessible)
- The paper is written in English by a non-native speaker (Italian)

---

**Editor's Note**: This is a faithful markdown conversion of the original PDF paper. The text preserves the author's original English, including grammatical variations. For detailed error analysis, see the README.md in the parent directory.
