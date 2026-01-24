# Renjit (2006) - co-NP=NP Proof Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 35 (Woeginger's list)
- **Author**: Raju Renjit G
- **Year**: 2006 (November)
- **Claim**: co-NP = NP
- **Paper**: http://arxiv.org/abs/cs.CC/0611147
- **Status**: **WITHDRAWN by author** (August 2009, after 9 revisions)

## Summary

In November 2006, Raju Renjit G published a paper claiming to prove **co-NP = NP**, meaning that the complexity classes NP and co-NP are equivalent. This would be a major breakthrough in computational complexity theory, though not as strong as resolving P vs NP directly.

The paper went through **9 revisions** over nearly three years before being **withdrawn by the author** on August 25, 2009. The withdrawal indicates that fundamental flaws were discovered that could not be repaired through revision.

## What is NP vs co-NP?

### Complexity Classes

- **NP**: Problems where "yes" answers can be verified in polynomial time
  - Example: CLIQUE - given a set of vertices, verify they form a clique
  - Certificate: The k vertices (polynomial size)

- **co-NP**: Problems where "no" answers can be verified in polynomial time
  - Example: NO-CLIQUE - verify a graph has no k-clique
  - Certificate needed: Proof that no k vertices form a clique (hard!)

### The Open Question

Whether **NP = co-NP** is unknown, but most researchers believe they are different because:

1. **Certificate Asymmetry**: Verifying existence (show one example) seems fundamentally easier than verifying non-existence (rule out all possibilities)
2. **Polynomial Hierarchy**: If NP = co-NP, the polynomial hierarchy collapses
3. **50+ Years of Research**: No symmetric certificate structures found despite extensive study
4. **Oracle Results**: There exist oracles relative to which NP ≠ co-NP

## Structure

This formalization follows the new repository structure:

### `original/`
Contains description of the original proof idea, approach, and why it seemed promising. Since the paper was withdrawn and is no longer available, this is reconstructed from:
- Available metadata (title, abstract, classification)
- The paper's focus on the clique problem (mentioned in metadata)
- The author's related 2005 P≠NP attempt (also clique-based, also withdrawn)
- Common patterns in NP = co-NP attempts

### `proof/`
Contains our best-effort forward proof attempt, following the likely strategy:
1. Focus on CLIQUE/NO-CLIQUE as canonical NP/co-NP-complete problems
2. Claim polynomial certificates exist for NO-CLIQUE (unproven!)
3. Attempt to generalize from CLIQUE to all NP problems (invalid!)
4. Conclude NP = co-NP

The formalizations mark WHERE the proof fails with:
- Axioms for unproven claims
- `sorry` / `Admitted` for gaps that cannot be filled
- Comments explaining the impossibility

### `refutation/`
Contains formal refutation demonstrating why the proof fails:
1. **Certificate Asymmetry**: Fundamental difference between verifying existence vs non-existence
2. **Invalid Generalization**: NP-completeness preserves decidability, not certificate structure
3. **Circular Reasoning**: Proposed verification reduces to another co-NP problem
4. **Special Cases**: Methods working for special graphs don't constitute universal proof

## The Core Error: Certificate Asymmetry

The fundamental challenge is the asymmetry between positive and negative witnesses:

**CLIQUE (NP)**:
- Instance: "Does graph G have a 5-clique?"
- YES Certificate: List the 5 vertices (polynomial size: 5 log n bits)
- Verification: Check all 10 edges exist (polynomial time: O(k²))

**NO-CLIQUE (co-NP)**:
- Instance: "Does graph G have NO 5-clique?"
- YES Certificate needed: Proof that no 5 vertices form a clique
- Challenge: Must reason about all (n choose 5) possibilities (exponential!)

For NP = co-NP to hold, we need polynomial-sized, polynomial-time verifiable certificates for BOTH directions for ALL problems in NP. The asymmetry suggests this is impossible.

## Common Error Patterns

### 1. Invalid Generalization from One Problem

**Error**: Proving a property for CLIQUE doesn't extend to all NP problems.

**Why**: Even though CLIQUE is NP-complete, reductions preserve **decidability** (x ∈ L ⟺ f(x) ∈ CLIQUE), not **certificate structure**. A certificate for x doesn't transform to a certificate for f(x).

### 2. Unproven Existence Claims

**Error**: Claiming polynomial NO-CLIQUE certificates exist without construction.

**Why**: Existence proofs aren't enough - must show certificates are polynomial-sized AND polynomial-time verifiable. All attempted constructions (vertex covers, edge covers, decompositions) either require exponential verification or are circular.

### 3. Circular Reasoning

**Error**: "Verifying NO-CLIQUE" by reducing to another co-NP problem.

**Why**: This just restates the challenge without making progress.

### 4. Special Cases vs Universal Proof

**Error**: Methods working for special graphs (trees, planar, dense) don't prove the general result.

**Why**: Must work for ALL instances, including adversarially constructed ones.

## Why the Paper Was Withdrawn

The withdrawal after **9 revision attempts** over **3 years** strongly suggests:

1. **Fundamental Error Discovered**: Not a minor technical issue
2. **Unrepairable Flaw**: Couldn't be fixed through revision
3. **Scientific Integrity**: Author chose withdrawal over leaving flawed work online
4. **Pattern**: Second withdrawal (2005 P≠NP also withdrawn, also clique-based)

This indicates the author recognized the core claim was flawed, not just the proof details.

## Formalization Files

### Refutation (Why it fails)
- `refutation/lean/RenjitRefutation.lean` - Lean 4 formalization of why NP = co-NP proofs fail
- `refutation/rocq/RenjitRefutation.v` - Rocq formalization of the refutation

### Forward Proof (Where it fails)
- `proof/lean/RenjitProof.lean` - Best-effort reconstruction showing gaps
- `proof/rocq/RenjitProof.v` - Rocq version marking impossibilities

## Educational Value

This formalization demonstrates:

1. **Reconstructing Historical Attempts**: Analyzing proof strategies from limited information
2. **Identifying Error Patterns**: Common mistakes in complexity proofs
3. **Understanding Reductions**: What NP-completeness does and doesn't imply
4. **Certificate Structures**: The fundamental asymmetry in NP vs co-NP
5. **Formal Verification**: Using proof assistants to expose gaps in informal proofs

## References

1. Woeginger, G. J. "The P-versus-NP page". Entry #35. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations.
3. Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P=?NP Question." SIAM Journal on Computing.
4. Arora, S., Barak, B. (2009). "Computational Complexity: A Modern Approach." Cambridge University Press.
5. Stockmeyer, L.J. (1976). "The polynomial-time hierarchy." Theoretical Computer Science.
6. Related: Renjit (2005) "Fixed Type Theorems" arXiv:cs/0502030 (also withdrawn, also clique-based)

---

**Note**: The original paper is no longer available (withdrawn from arXiv). Our formalization is a reconstruction based on available metadata and common error patterns in such attempts. The goal is educational: understanding why such proofs fail helps avoid similar mistakes and appreciate the difficulty of these fundamental questions.
