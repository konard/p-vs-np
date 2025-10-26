# Joonmo Kim (2014) - P≠NP Proof Attempt

**Attempt ID**: 100
**Author**: Joonmo Kim
**Year**: 2014
**Claim**: P≠NP
**Paper**: [arXiv:1403.4143v7](https://arxiv.org/abs/1403.4143)
**Status**: **REFUTED**

## Summary

In March 2014, Joonmo Kim submitted a proof claiming that P is not equal to NP. The proof attempts to use a modus tollens argument involving an artificially designed Turing Machine M° that generates instances of the satisfiability problem and checks their satisfiability. The author claimed that under the assumption P = NP, this machine has a certain property (that it can be implemented with a deterministic polynomial-time SAT solver), which it does not have without the assumption, leading to a contradiction.

**Important Note**: The author himself acknowledged in the paper's abstract that "it is quite unlikely that this simple solution is correct" and explicitly stated "Author does not expect the success of the proof, rather he is waiting to see what is wrong."

## Main Argument

The proof uses a modus tollens structure: `(P1 → (P2 → P3)) ∧ (¬(P2 → P3))` concludes `¬P1`, where:

- **P1**: P = NP
- **P2**: M° exists (a special Turing machine with specific properties)
- **P3**: There exists a transition table t which is Dsat (deterministic polynomial-time)

### Construction of M and M°

1. **M family**: Kim defines a family of Turing machines M₁, M₂, ..., Mᵢ, ... where each Mᵢ:
   - Contains embedded "run-parts" (c^r) from SAT encodings of accepting computations
   - Takes input y and creates c^y (the input-part encoding)
   - Concatenates c^y with each c^r to form complete SAT instances
   - Runs a SAT solver on each instance
   - Accepts if an odd number of instances are satisfiable

2. **M°**: A special machine from the M family where:
   - Let ac_M be the accepting computation of M on input y
   - Let t be a particular transition table for ac_M
   - Let c° be one of the SAT instances appearing during M's run
   - Let ac_c° be the accepting computation described by c°
   - If t is also a particular transition table for ac_c°, then M is designated as M°

3. **Dsat and NDsat**: Two types of particular transition tables:
   - **Dsat**: M° runs deterministically with a polynomial-time SAT solver
   - **NDsat**: M° runs non-deterministically with a polynomial-time SAT solver

### The Proof Strategy

**Part 1**: Show P1 → (P2 → P3)
- If P = NP, then polynomial-time SAT solvers exist
- Therefore, if M° exists, it can use a deterministic polynomial-time SAT solver
- Thus t can be Dsat

**Part 2**: Show ¬(P2 → P3) by contradiction
- Claim: M° can exist with NDsat transition table (by merging two non-deterministic tables)
- Assume P2 → P3 (if M° exists, then Dsat transition table exists)
- This implies ac_M° and ac_c° are the same computation
- Let i = number of transitions in ac_M°
- Let j = number of clauses in c°
- Let k = number of transitions in ac_c°
- Argue: i > j (all clauses must be loaded on tape) and j > k (each transition needs multiple clauses)
- Therefore i > j > k
- But if ac_M° = ac_c°, then i = k
- **Contradiction!**

## The Error

The proof was refuted by Hassin, Scrivener, and Zhou in "[Critique of J. Kim's 'P is not equal to NP by Modus Tollens'](https://arxiv.org/abs/1404.5352)" (2014). The critique identifies **multiple fatal flaws**:

### 1. **Logical Inconsistency** (Section 3.1)

The proof's central contradiction doesn't actually use the Dsat property of t. The assumption "if M° exists then Dsat exists" is logically equivalent to "M° exists ⇒ t exists". However, **by definition**, M° exists if and only if t exists. Therefore, Kim cannot possibly prove that "(M° exists) ⇒ (t exists)" is false. This is a fundamental logical error.

### 2. **Ambiguous Definition of Accepting Computations** (Section 3.2)

Kim's definition of "accepting computation" is critically ambiguous. There are two reasonable interpretations:

**Interpretation 1**: An accepting computation is produced by a Turing machine's own transition table
- Under this interpretation, ac_M° and ac_c° come from entirely different machines
- Kim's "merging" technique to create a shared transition table is invalid because:
  - The merged table contains new states (union of states from both machines)
  - It operates on a different state space than either original machine
  - It cannot be considered the "same" transition function as either machine
- Therefore, the merged table doesn't actually prove that ac_M° and ac_c° are the same computation
- The inequality i > j > k holds without contradiction

**Interpretation 2**: An accepting computation can be produced by any particular transition table
- Under this interpretation, ac_M° and ac_c° produced by t ARE the same computation
- But then the analysis based on their respective original machines doesn't apply
- The claim i > j > k doesn't follow because we're now talking about the same computation produced by t
- There is no contradiction

**Critical Issue**: Kim appears to switch between interpretations mid-proof—using Interpretation 1 to establish i > j > k, then using Interpretation 2 to claim i = k. This inconsistency invalidates the proof.

### 3. **The "Merging" Technique is Ill-Formed**

Kim claims to merge two transition tables to create a non-deterministic table that can produce both computations. However:
- The merged table has a different state space (includes states from both machines)
- It may have different alphabet symbols
- It is not a valid transition table for either original machine
- This technique doesn't establish that the same transition table works for both computations in any meaningful sense

### 4. **i > j > k Analysis is Problematic**

The counting argument has issues:
- i counts transitions in the entire run of M° on input y
- j counts clauses in c° (one specific SAT instance among many)
- k counts transitions in the computation described by c°
- These quantities are measuring different things at different levels of abstraction
- The relationship i > j assumes all clauses of c° must be "loaded on tape," but this conflates the meta-level computation of M° with the object-level computation encoded in c°

## Why This Matters

This proof attempt is valuable as a case study because:

1. **Self-Aware**: The author explicitly acknowledged uncertainty about correctness
2. **Common Pattern**: Demonstrates a common error in P vs NP attempts—conflating different levels of computation (meta-level vs object-level)
3. **Definitional Precision**: Shows how ambiguous definitions can lead to invalid proofs
4. **Logical Structure**: Illustrates how modus tollens arguments can fail when assumptions are circular
5. **Quick Refutation**: The community quickly identified and published a detailed refutation

## Formalization Goals

The formalizations in this directory aim to:

1. **Model the constructions**: Formalize the M family, M°, and transition table concepts
2. **Capture the ambiguity**: Make explicit the two interpretations of "accepting computation"
3. **Expose the error**: Show where the proof breaks down under each interpretation
4. **Demonstrate the circularity**: Formalize why "M° exists iff t exists" makes the contradiction impossible

## Key Lessons

1. **Definitional Rigor**: Every definition must be precise and unambiguous
2. **Level Confusion**: Be careful not to confuse computations at different meta-levels
3. **Circular Definitions**: Watch for circular dependencies in definitions
4. **Self-Reference**: The construction involves machines that embed SAT instances, creating self-referential complexity that must be handled carefully
5. **Modus Tollens Pitfalls**: Ensure that assumptions in modus tollens arguments are actually independent

## References

1. Joonmo Kim. "P ≠ NP by Modus Tollens." arXiv:1403.4143v7 [cs.CC], October 2018. https://arxiv.org/abs/1403.4143
2. Dan Hassin, Adam Scrivener, and Yibo Zhou. "Critique of J. Kim's 'P is not equal to NP by Modus Tollens'." arXiv:1404.5352v2 [cs.CC], April 2014. https://arxiv.org/abs/1404.5352
3. M. R. Garey and D. S. Johnson. "Computers and Intractability: A Guide to the Theory of NP-Completeness." W. H. Freeman & Co., 1979.
4. Woeginger's P-versus-NP page: https://www.win.tue.nl/~gwoegi/P-versus-NP.htm (Entry #100)

## Directory Structure

```
joonmo-kim-2014-pneqnp/
├── README.md (this file)
├── coq/
│   └── JoonmoKim2014.v (Coq formalization)
├── lean/
│   └── JoonmoKim2014.lean (Lean formalization)
└── isabelle/
    └── JoonmoKim2014.thy (Isabelle formalization)
```

## Formalization Status

- [x] README documentation complete
- [ ] Coq formalization in progress
- [ ] Lean formalization in progress
- [ ] Isabelle formalization in progress

---

**Conclusion**: This proof attempt fails due to fundamental logical errors, ambiguous definitions, and inconsistent interpretation of key concepts. The formalization work helps make these errors explicit and provides a learning resource for understanding common pitfalls in complexity theory proofs.
