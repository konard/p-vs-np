# Yubin Huang (2015) - P=NP Attempt

**Attempt ID**: 105 (Woeginger's list entry #110)
**Author**: Yubin Huang
**Year**: 2015
**Claim**: P = NP
**Paper**: [Testing a new idea to solve the P = NP problem with mathematical induction](https://peerj.com/preprints/1455/)
**Status**: Refuted

## Summary

In October 2015, Yubin Huang published a preprint claiming to prove P = NP by introducing a method to reduce nondeterministic computation complexity. The main claim is: "For any language L accepted by a non-deterministic Turing machine in polynomial time, there exists a deterministic Turing machine that accepts L in polynomial time."

## Main Argument

The proof attempt is based on the following approach:

1. **Filter Function**: Define a filter function `C(M,w)` that measures the number of nondeterministic moves in a Turing machine `M` on input `w`. Specifically, `C(M,w)` counts the number of configurations that have more than one child (nondeterministic moves) in the shortest accept computation path.

2. **Restricted Turing Machines**: Construct a "restricted Turing machine" whose maximum number of nondeterministic moves in the accept computation tree of inputs is limited.

3. **Hierarchy of Classes**: Establish a hierarchy of language classes `L_i(M)` associated with natural numbers between P and NP:
   - Each class `L_i(M)` contains languages with at most `i` nondeterministic moves
   - P forms the lowest hierarchy level (L_0)
   - Any language in NP is accepted by machines in each of these classes

4. **Key Claim**: Attempt to show that `L_{i+1}`, which seems more powerful, can be proved to be a subset of `L_i`, ultimately collapsing the hierarchy to show NP ⊆ P.

5. **Multi-tape Simulation**: Use a multi-tape Turing machine to simulate and reduce nondeterministic moves.

## The Error

The fundamental error in this proof attempt lies in the **unjustified hierarchy collapse**. The proof makes several critical mistakes:

### 1. **Invalid Reduction Argument**

The claim that `L_{i+1} ⊆ L_i` is not rigorously proven. The author suggests that a more powerful machine (allowing more nondeterministic moves) can be simulated by a less powerful one, but this is precisely what needs to be proven, not assumed.

**Why this fails**: Simply defining a hierarchy doesn't prove it collapses. The author needs to show that for each nondeterministic move, there exists a deterministic simulation that doesn't increase the complexity beyond polynomial bounds. This is exactly the hard part of the P vs NP problem.

### 2. **Circular Reasoning**

The proof essentially assumes what it tries to prove. By claiming that languages with more nondeterministic moves can be reduced to languages with fewer moves while maintaining polynomial time, the author is assuming that nondeterminism doesn't add computational power - which is equivalent to assuming P = NP.

### 3. **Missing Polynomial Time Bound**

Even if each nondeterministic move could be eliminated, the proof doesn't establish that doing so maintains polynomial time complexity. Each "level" reduction might multiply the time complexity, potentially leading to exponential time overall.

**Critical gap**: If eliminating one nondeterministic move requires trying multiple paths, and there are `k` such moves, the total time could be `O(b^k)` where `b` is the branching factor - exponential, not polynomial.

### 4. **Ignoring Known Barriers**

The proof attempt doesn't address any of the known barriers to resolving P vs NP:
- **Relativization**: The technique would need to work in all oracle worlds
- **Natural Proofs**: The approach appears to be "natural" in the Razborov-Rudich sense
- **Algebrization**: The method doesn't account for algebrization barriers

### 5. **Lack of Rigorous Formalization**

The preprint lacks:
- Precise mathematical definitions of the hierarchy
- Formal proof of the subset relationships
- Explicit construction of the deterministic machines
- Time complexity analysis

## Formalization Goal

Our goal is to formalize this proof attempt in Coq, Lean, and Isabelle until we hit the fundamental gap. We expect to be able to formalize:

✅ The definition of the filter function `C(M,w)`
✅ The hierarchy of language classes `L_i`
✅ The statement that `L_0 = P`
✅ The claim that every language in NP is in some `L_k`

We expect to **fail** when trying to prove:

❌ `L_{i+1} ⊆ L_i` with polynomial time preservation
❌ The collapse of the hierarchy to `L_0`
❌ NP ⊆ P

## Implementation

- **Coq**: [coq/HuangAttempt.v](coq/HuangAttempt.v)
- **Lean**: [lean/HuangAttempt.lean](lean/HuangAttempt.lean)
- **Isabelle**: [isabelle/HuangAttempt.thy](isabelle/HuangAttempt.thy)

## References

1. **Original Paper**: Huang, Y. (2015). "Testing a new idea to solve the P = NP problem with mathematical induction." PeerJ Preprints. https://peerj.com/preprints/1455/

2. **Woeginger's List**: Entry #110. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

3. **Parent Issue**: #44 - Test all P vs NP attempts formally

## Related Work

This attempt is similar to other failed P = NP proofs that try to:
- Establish hierarchies between P and NP
- Show that nondeterministic moves can be systematically eliminated
- Use induction without properly accounting for time complexity

The key lesson: **Defining a hierarchy doesn't prove it collapses**, and eliminating nondeterminism typically requires exponential search.

---

*Formalized as part of the P vs NP educational research repository.*
