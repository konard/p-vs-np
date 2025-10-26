# Joonmo Kim (2014) - P≠NP Proof Attempt

**Attempt ID**: 100 (from Woeginger's list)
**Author**: Joonmo Kim
**Affiliation**: Applied Computer Engineering Department, Dankook University, South Korea
**Year**: 2014
**Claim**: P ≠ NP
**ArXiv**: [1403.4143](http://arxiv.org/abs/1403.4143)
**Status**: Refuted

## Summary

Joonmo Kim's 2014 paper "P ≠ NP by Modus Tollens" attempts to prove P ≠ NP using a proof by contradiction via modus tollens. The proof constructs an artificially designed Turing Machine algorithm M^o that generates instances of the satisfiability problem (SAT) and checks their satisfiability. The author claims that under the assumption P = NP, M^o would have a certain property (namely, the existence of a deterministic polynomial-time particular transition table), which it does not have without this assumption, thereby deriving a contradiction.

**Important Note**: The author himself acknowledged significant uncertainty about the proof's validity, stating explicitly in early versions: "this solution should not be reported to be correct" and noting it is "quite unlikely that this simple solution is correct."

## Main Argument/Approach

The proof uses the logical form of modus tollens:
- (P₁ → (P₂ → P₃)) ∧ (¬(P₂ → P₃)) ⇒ ¬P₁

Where:
- **P₁**: P = NP
- **P₂**: M^o exists
- **P₃**: there exists t (a particular transition table), which is D_sat

### Key Definitions

1. **Cook's Encoding Extension**: The proof extends Cook's theorem to represent not just polynomial-time computations but any finite-length accepting computation as SAT instances, regardless of runtime.

2. **SAT Instance Structure**: Each SAT instance c is divided into:
   - **c^x** (input-part): Clauses describing the input x
   - **c^r** (run-part): Clauses representing the Turing machine operations (groups G₁, G₂, G₃, G₅, G₆ from Cook's encoding)

3. **Algorithm M_i**: A Turing machine that:
   - Contains a finite number of run-parts c^r₁, ..., c^r_n extracted from accepting computations
   - On input y, concatenates c^y with each c^r_ij to form c_ij
   - Uses a SAT-solver module to check satisfiability of each c_ij
   - Accepts y if an odd number of the c_ij's are satisfiable

4. **Algorithm M^o**: A special instance of M where:
   - Let ac_M be the accepting computation of M on input y
   - Let t be a particular transition table for ac_M
   - Let c^o be one of the SAT instances appearing during M's run
   - Let ac_{c^o} be the accepting computation described by c^o
   - If t is also a particular transition table for ac_{c^o}, then M is designated as M^o

5. **Transition Table Types**:
   - **D_sat**: Particular transition table where M^o runs deterministically and the SAT-solver runs in deterministic polynomial time
   - **ND_sat**: Particular transition table where M^o runs non-deterministically and the SAT-solver runs in non-deterministic polynomial time

### Proof Structure

**Part 1**: Prove P₁ → (P₂ → P₃)
- Assumes P = NP
- Therefore, there exists a deterministic polynomial-time SAT solver
- Thus, M^o can be implemented with a D_sat transition table
- Conclusion: If M^o exists, then D_sat exists

**Part 2**: Prove ¬(P₂ → P₃)
- First, show P₂ is true: For any chosen c^o, build two non-deterministic particular transition tables for ac_{M^o} and ac_{c^o} separately, then merge them so that one can be selected at runtime. Thus M^o exists via this ND_sat table.
- Second, derive a contradiction from P₂ → P₃:
  - If P₂ → P₃, then there exists a D_sat table for both ac_{M^o} and ac_{c^o}
  - Since they share the same input, they would be exactly the same computation
  - Let i = number of transitions in ac_{M^o}
  - Let j = number of clauses in c^o
  - Let k = number of transitions in ac_{c^o}
  - The proof claims: i > j (M^o must load all clauses plus other operations)
  - And: j > k (Cook's theorem states each transition needs multiple clauses)
  - Therefore: i > j > k
  - But if ac_{M^o} and ac_{c^o} are identical, then i = k
  - This is a contradiction

**Conclusion**: By modus tollens, P ≠ NP.

## Known Refutation

The proof was critiqued by Hassin, Scrivener, and Zhou in their 2014 arXiv paper ["Critique of J. Kim's 'P is not equal to NP by Modus Tollens'"](http://arxiv.org/abs/1404.5352). The critique identifies several fundamental logical inconsistencies and definitional problems.

## The Error in the Proof

The proof contains several critical flaws:

### 1. **Ambiguous and Self-Referential Definitions**

The definition of M^o is circular and poorly specified:
- M^o is defined as a machine M where the particular transition table t for M's accepting computation ac_M is also a particular transition table for some SAT instance c^o that appears during M's run
- But whether c^o appears during M's run depends on what transition table M uses
- This creates a circular dependency: M^o's identity depends on what happens during its run, which depends on what M^o is

### 2. **Confusion Between Transition Tables and Computations**

The proof conflates:
- **Transition tables** (the fixed program/specification of a Turing machine)
- **Computations** (the dynamic execution traces)
- **Particular transition tables** (an undefined concept that seems to mean "transition tables for specific instances")

A "particular transition table for an accepting computation" is not a standard or well-defined concept. A transition table is a static specification, while a computation is a dynamic trace. The proof attempts to reason about "particular transition tables" as if they capture specific computation traces, but this is conceptually confused.

### 3. **Invalid Inequality i > j > k**

The proof's central inequality chain is flawed:

**Claim: i > j**
- i = number of transitions in ac_{M^o}
- j = number of clauses in c^o
- The argument is that "all clauses of c^o should once be loaded on the tape"

**Problem**: This doesn't imply i > j. The number of clauses in a SAT encoding and the number of transitions in a computation are incommensurable quantities. A Turing machine doesn't necessarily have one transition per clause; it might process multiple clauses per transition, or spend multiple transitions on a single clause. There's no theorem stating i > j.

**Claim: j > k**
- j = number of clauses in c^o
- k = number of transitions in ac_{c^o}
- The argument cites Cook's theorem that "each transition is described by more than one clauses"

**Problem**: This actually suggests k < j, not j > k. But the proof needs j > k for the inequality chain. Moreover, this relationship is about encoding direction (computation → SAT), not the reverse (SAT → computation). The proof uses j and k in a way that doesn't correspond to how Cook's encoding works.

### 4. **Equivocation on "Same Computation"**

The proof argues that if D_sat exists for both ac_{M^o} and ac_{c^o} with the same input, then they are "exactly the same computation." This is a non-sequitur:
- ac_{M^o} is the accepting computation of M^o on input y
- ac_{c^o} is the accepting computation **described by the SAT instance c^o** (which is a totally different computation - it's whatever computation c^o encodes, unrelated to M^o)
- These are fundamentally different computations; there's no reason they would be identical

### 5. **Misunderstanding of "Particular Transition Tables"**

The proof introduces "particular transition tables" without rigorous definition. In Version 7's addendum, the author attempts to clarify by introducing the notion of "All Poly Machine" (APM) and stating that particular transition tables must be implementable by the designated APM. However, this clarification:
- Introduces additional undefined concepts
- Makes the proof even more circular (whether DTM or NDTM is the APM depends on whether P = NP, which is what we're trying to prove)
- Obscures rather than illuminates the logical structure

### 6. **Non-Standard Use of Cook's Theorem**

The proof extends Cook's theorem to non-polynomial-time computations "as long as the run is finite." While this extension is technically possible, the proof then tries to reason about polynomial-time properties (D_sat) for these potentially exponential-time objects, creating a mismatch.

### 7. **The Modus Tollens Application is Invalid**

Even if we granted all the definitions and claims, the modus tollens structure fails:
- To prove ¬(P₂ → P₃), the proof shows P₂ ∧ (P₂ → P₃) leads to contradiction
- But the "contradiction" i > j > k and i = k relies on all the flawed reasoning above
- Without a valid contradiction, ¬(P₂ → P₃) is not established
- Therefore, the modus tollens conclusion doesn't follow

## Formalization Insights

Our formalization attempts (in Coq, Lean, and Isabelle) aim to expose these errors by:

1. **Attempting to formally define "particular transition table"** - This quickly reveals the concept is not well-defined
2. **Formalizing the inequality i > j > k** - This shows there's no theorem supporting these relationships
3. **Modeling M^o's definition** - This exposes the circular dependency
4. **Checking the modus tollens structure** - This reveals that the premises are not proven

The formalization process demonstrates that the proof cannot be completed because the fundamental definitions and lemmas are either circular, ambiguous, or simply false.

## Lessons Learned

This proof attempt illustrates several common pitfalls in P vs NP proof attempts:

1. **Informal definitions that seem plausible in natural language but cannot be formalized**
2. **Self-referential constructions that lead to circular reasoning**
3. **Mixing different levels of abstraction** (syntax vs. semantics, programs vs. executions)
4. **Assuming relationships between quantities without rigorous justification**
5. **Using standard results (like Cook's theorem) in non-standard ways**

## References

1. Joonmo Kim. "P is not equal to NP by Modus Tollens." arXiv:1403.4143v7 [cs.CC], October 2018. [https://arxiv.org/abs/1403.4143](https://arxiv.org/abs/1403.4143)

2. Dan Hassin, Adam Scrivener, and Yibo Zhou. "Critique of J. Kim's 'P is not equal to NP by Modus Tollens'." arXiv:1404.5352 [cs.CC], April 2014. [https://arxiv.org/abs/1404.5352](https://arxiv.org/abs/1404.5352)

3. M. R. Garey and D. S. Johnson. "Computers and Intractability: A Guide to the Theory of NP-Completeness." W. H. Freeman & Co., New York, 1979.

4. Woeginger's P-versus-NP page: [https://www.win.tue.nl/~gwoegi/P-versus-NP.htm](https://www.win.tue.nl/~gwoegi/P-versus-NP.htm) (Entry #100)

## See Also

- [Parent Issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue #316](https://github.com/konard/p-vs-np/issues/316) - This formalization task
