# Raju Renjit (2006) - Original Proof Idea

## The Claim

Raju Renjit claimed to prove **co-NP = NP**, meaning that the complexity classes NP and co-NP are equivalent.

## Core Approach

### Step 1: Target NP vs co-NP via the Clique Problem

Based on available metadata and the author's related 2005 P≠NP attempt (which also focused on the clique problem), Renjit's approach likely centered on analyzing:

**The Clique Problem Pair:**
- **CLIQUE (NP-complete)**: Given graph G and integer k, does G contain a clique of size at least k?
- **NO-CLIQUE (co-NP-complete)**: Given graph G and integer k, does G contain NO clique of size at least k?

### Step 2: Develop a General Theoretical Result

The paper claimed to develop a general result showing some form of equivalence or symmetry between NP and co-NP. The exact nature of this claimed result is unknown since the paper is no longer available.

Typical approaches in such attempts include:
- Claiming efficient certificates exist for both positive and negative instances
- Arguing that complement problems have symmetric verification complexity
- Attempting to show that NP-complete and co-NP-complete problems have equivalent structure

### Step 3: Apply to Clique as Demonstration

The clique problem likely served as the concrete example demonstrating the general result:
- Show that CLIQUE and NO-CLIQUE have some claimed symmetric property
- Use this to support the general NP = co-NP claim

### Step 4: Conclude co-NP = NP

From the claimed general result and its application to clique, conclude that NP = co-NP.

## Why This Approach Seemed Promising

The clique problem pair has several features that make it seem like a natural target:

1. **Structural Duality**: CLIQUE and NO-CLIQUE are exact complements
2. **Both Complete**: CLIQUE is NP-complete, NO-CLIQUE is co-NP-complete
3. **Intuitive Appeal**: Cliques are well-understood graph-theoretic objects
4. **Prior Work**: The author had already studied this problem in the 2005 P≠NP attempt

## The Fundamental Challenge: Certificate Asymmetry

The critical obstacle that such proofs must overcome is the **asymmetry between positive and negative witnesses**:

### For CLIQUE (NP):
- **YES Instance**: "This graph HAS a 5-clique"
- **Certificate**: The 5 vertices forming the clique
- **Verification**: Check all (5 choose 2) = 10 edges exist - **polynomial time**
- **Certificate Size**: 5 vertices - **polynomial in input size**

### For NO-CLIQUE (co-NP):
- **NO Instance**: "This graph has NO 5-clique"
- **Certificate**: Must prove no set of 5 vertices forms a clique
- **Verification Challenge**: Need to reason about all (n choose 5) possible 5-vertex subsets
- **Typical Approach**: Requires exponential reasoning or sophisticated proof techniques

**Key Principle**: For NP = co-NP to hold, we need efficient (polynomial-sized, polynomial-time verifiable) certificates for BOTH positive and negative instances of ALL NP problems.

## Common Pitfalls in NP = co-NP Attempts

### 1. Invalid Generalization from One Problem

**Error**: Showing a property for the clique problem doesn't automatically prove it for all NP/co-NP problems.

**Why**: While CLIQUE is NP-complete, reductions preserve **decidability**, not **certificate structure**. Even if you could show symmetric certificates for CLIQUE and NO-CLIQUE, this doesn't transfer through reductions to other problems.

### 2. Confusion Between Search and Verification

**Error**: Conflating the ability to find solutions with the ability to verify solutions.

**Why**: NP is defined by efficient **verification**, not efficient **search**. Being able to find a clique efficiently (if we could) doesn't address whether we can efficiently verify a graph has no clique.

### 3. Missing the Efficiency Requirement

**Error**: Showing that a certificate exists without proving it's polynomial-sized and polynomial-time verifiable.

**Why**: For a problem to be in co-NP, we need **efficient** certificates for "no" instances. Existential proofs (showing some certificate exists) don't suffice without concrete bounds on size and verification time.

### 4. Incomplete Correctness Analysis

**Error**: The claimed result works for special cases but fails on general instances.

**Why**: A valid proof must work for ALL instances of ALL problems in NP, not just specific graph structures or particular problems.

## Source Material Status

**Original Paper**: arXiv:cs.CC/0611147 (WITHDRAWN)
**Title**: "coNP Is Equal To NP"
**Author**: Raju Renjit G
**Publication**: November 2006 (initial), withdrawn August 2009
**Availability**: No longer accessible (withdrawn by author)
**Revisions**: 9 versions (v1 through v8)

The paper is no longer available for download from arXiv. The arXiv page shows:
> "This submission has been withdrawn at the request of the author."

## What We Know From Historical Records

From Woeginger's P vs NP list (Entry #35) and arXiv metadata:
- **Claim**: co-NP = NP
- **Approach**: General theoretical result applied to clique problem
- **Field**: Computational Complexity (cs.CC)
- **Length**: 24 pages (version 1)
- **Timeline**:
  - November 29, 2006: Initial submission (v1)
  - 2006-2009: Nine revisions (v1-v8)
  - August 25, 2009: Withdrawn by author

## Significance of the Withdrawal

The withdrawal after **9 revision attempts** over **3 years** is highly significant:

1. **Author Recognition of Error**: The author discovered a fundamental flaw in the proof
2. **Unrepairable**: The error couldn't be fixed through revisions
3. **Scientific Integrity**: The author chose to withdraw rather than leave a flawed proof online
4. **Pattern**: This was the author's second withdrawal (2005 P≠NP attempt also withdrawn)

This strongly suggests the proof contained a deep conceptual error, not just a minor technical mistake.

## Why NP = co-NP is Believed False

The complexity theory community generally believes NP ≠ co-NP because:

1. **Polynomial Hierarchy**: If NP = co-NP, the polynomial hierarchy collapses to its first level
2. **Certificate Intuition**: Verifying existence seems fundamentally easier than verifying non-existence
3. **Oracle Results**: There exist oracles relative to which NP ≠ co-NP (though also oracles where they're equal)
4. **50+ Years of Research**: No one has found symmetric certificate structures despite extensive study
5. **Weaker Than P vs NP**: Even if true, wouldn't resolve P = NP (though would be major breakthrough)

## References

1. Woeginger, G. J. "The P-versus-NP page". Entry #35. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations.
3. Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P=?NP Question." SIAM Journal on Computing.
4. Arora, S., Barak, B. (2009). "Computational Complexity: A Modern Approach." Cambridge University Press.
5. Related work: Renjit (2005) "Fixed Type Theorems" arXiv:cs/0502030 (also withdrawn)
