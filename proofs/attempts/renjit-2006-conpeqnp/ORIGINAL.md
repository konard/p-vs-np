# Original Paper: co-NP Is Equal To NP

**Author:** Raju Renjit G
**Year:** 2006 (submitted November 29, 2006)
**arXiv ID:** [cs/0611147](https://arxiv.org/abs/cs/0611147)
**Woeginger's List:** Entry #35
**Status:** **WITHDRAWN** by author (August 25, 2009)

---

## Paper Availability

⚠️ **This paper is no longer available for download.**

The paper was withdrawn by the author on August 25, 2009, after undergoing 9 revision attempts over approximately 2.8 years. The arXiv page currently shows:

> "This submission has been withdrawn at the request of the author."

No PDF is accessible, and the paper content cannot be retrieved.

---

## Metadata Discrepancy

There is a discrepancy between the arXiv title and Woeginger's list:

- **Woeginger's List Entry #35**: "co-NP Is Equal To NP" (claims co-NP = NP)
- **arXiv Page Title**: "P is not equal to NP" (claims P ≠ NP)

This discrepancy may have occurred because:
1. The paper was extensively revised (9 versions)
2. The author may have changed the claim between versions
3. The arXiv title may have been updated after earlier versions
4. The author had two related papers: one in 2005 claiming P≠NP (entry #20), and this 2006 paper

According to Woeginger's detailed notes on entry #35:
> "By investigating the clique problem, the author recognizes that there exists a case where the time complexity of NP and co-NP are the same in the worst case."

This confirms the paper's actual claim was **co-NP = NP**, not P ≠ NP.

---

## What We Know From Historical Records

### From Woeginger's List (Entry #35)

**Main Claim:** co-NP = NP

**Approach:** "By investigating the clique problem, the author recognizes that there exists a case where the time complexity of NP and co-NP are the same in the worst case."

**Key Problem:** The CLIQUE problem pair:
- **CLIQUE (NP-complete)**: Given graph G and integer k, does G contain a clique of size at least k?
- **NO-CLIQUE (co-NP-complete)**: Given graph G and integer k, does G contain NO clique of size at least k?

### From arXiv Metadata

**Revision History:**
- **Version 1**: November 29, 2006 (12 KB)
- **Version 2**: November 19, 2007 (18 KB) - 1 year later
- **Versions 3-8**: April-June 2009 (14-20 KB) - Multiple rapid revisions
- **Version 9**: August 25, 2009 (1 KB) - Withdrawn

**Subject:** Computational Complexity (cs.CC)

**DOI:** https://doi.org/10.48550/arXiv.cs/0611147

---

## Reconstructed Proof Approach

Since the paper is unavailable, we reconstruct the likely approach based on:
1. Woeginger's description: "investigating the clique problem"
2. The claim that "time complexity of NP and co-NP are the same in the worst case"
3. Common error patterns in similar attempts
4. The author's 2005 P≠NP paper (also focused on clique, also withdrawn)

### Likely Step 1: Analyze CLIQUE Problem

The author probably started by analyzing the computational structure of:
- **CLIQUE**: Verify that a k-clique exists (NP)
- **NO-CLIQUE**: Verify that no k-clique exists (co-NP)

### Likely Step 2: Claim Symmetric Complexity

The author may have claimed to show that:
- Both CLIQUE and NO-CLIQUE have the same worst-case time complexity
- This symmetric complexity extends to their certificate structures
- Therefore, both problems have efficient verification procedures

### Likely Step 3: Generalize to All NP/co-NP

From the clique example, generalize:
- Since CLIQUE is NP-complete and NO-CLIQUE is co-NP-complete
- Any symmetric property for these problems should extend to all NP and co-NP
- Therefore, NP = co-NP

### Likely Step 4: Conclude co-NP = NP

Conclude that the complexity classes are identical.

---

## Why This Reasoning Fails

### Error #1: Certificate Asymmetry

The fundamental problem is that **positive and negative certificates are asymmetric**:

**CLIQUE (NP):**
- **YES Instance**: "This graph HAS a 5-clique"
- **Certificate**: List the 5 vertices: {v₁, v₂, v₃, v₄, v₅}
- **Verification**: Check all C(5,2) = 10 edges exist → **O(k²) time**, polynomial
- **Certificate Size**: k vertices → **polynomial**

**NO-CLIQUE (co-NP):**
- **NO Instance**: "This graph has NO 5-clique"
- **Certificate**: Need to prove no 5-vertex subset forms a clique
- **Naive Verification**: Check all C(n,5) possible subsets → **exponential**
- **Challenge**: No known polynomial certificate exists for general graphs

Even if worst-case *running time* is similar (both might require exploring the entire search space), **certificate complexity** is different.

### Error #2: Worst-Case Time ≠ Certificate Complexity

The statement "time complexity of NP and co-NP are the same in the worst case" conflates:
- **Worst-case running time** (how long an algorithm takes)
- **Certificate verification time** (NP's defining characteristic)

NP is defined by **efficient verification**, not efficient solving. Even if solving both CLIQUE and NO-CLIQUE takes exponential time in the worst case, this doesn't address whether efficient **certificates** exist for negative instances.

### Error #3: NP-Completeness Preserves Decidability, Not Certificates

Showing a property for CLIQUE doesn't automatically extend to all NP problems because:
- Reductions preserve **decidability** (if you can solve CLIQUE, you can solve SAT)
- Reductions **do not** preserve **certificate structure** (CLIQUE certificates don't map to SAT certificates in any simple way)

Even if we had symmetric certificates for CLIQUE/NO-CLIQUE, this doesn't transfer through polynomial-time reductions.

### Error #4: Special Cases Don't Constitute Proof

The phrase "there exists a case where..." suggests the proof may only work for:
- Special graph structures (e.g., complete graphs, empty graphs, regular graphs)
- Specific parameter values
- Particular algorithmic approaches

A valid proof must work for **all instances** of **all problems** in the complexity classes.

---

## Significance of the Withdrawal

The withdrawal after **9 revision attempts** over **2.8 years** strongly indicates:

1. **Author Recognition**: The author discovered fundamental flaws
2. **Unrepairable**: The errors couldn't be fixed through multiple revision attempts
3. **Scientific Integrity**: The author chose to withdraw rather than leave flawed work online
4. **Pattern**: This is the author's second withdrawal (2005 P≠NP attempt also withdrawn)
5. **Deep Error**: Not a minor technical mistake, but a conceptual flaw

The extensive revision history (especially the rapid sequence in 2009) suggests the author made serious efforts to repair the proof before ultimately recognizing it was fundamentally flawed.

---

## Why NP = co-NP is Believed False

The complexity theory community generally believes **NP ≠ co-NP** because:

1. **Certificate Asymmetry**: Verifying existence vs. non-existence seem fundamentally different
2. **Polynomial Hierarchy**: If NP = co-NP, the entire polynomial hierarchy collapses to Σ₁ᴾ = Π₁ᴾ
3. **Oracle Separation**: There exist oracles relative to which NP ≠ co-NP
4. **No Progress in 50+ Years**: Despite extensive research, no symmetric certificate structures found
5. **Weaker Than P vs NP**: Even if true, wouldn't resolve P = NP (P could still be strictly smaller)

---

## Related Work

**Author's Previous Attempt:**
- **Entry #20** (Woeginger's list): Raju Renjit (2005) "Fixed Type Theorems"
- **arXiv:** cs/0502030
- **Claim:** P ≠ NP
- **Status:** Also withdrawn
- **Approach:** Also focused on the clique problem

The pattern of two withdrawn papers on related topics, both focusing on clique, suggests a recurring conceptual error in the author's approach to complexity class separations.

---

## References

1. **Woeginger's P vs NP page**, Entry #35: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. **arXiv page** (withdrawn): https://arxiv.org/abs/cs/0611147
3. **DOI**: https://doi.org/10.48550/arXiv.cs/0611147
4. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." *Complexity of Computer Computations*.
5. Papadimitriou, C.H. (1994). "Computational Complexity." Addison-Wesley.
6. Arora, S., Barak, B. (2009). "Computational Complexity: A Modern Approach." Cambridge University Press.

---

## Note on Formalization

Since the original paper is unavailable, our formalization in `/proof/` and `/refutation/` folders is based on:
- Woeginger's brief description
- Common error patterns in similar attempts
- General principles of complexity theory
- The author's related 2005 paper (which is also withdrawn but has some historical documentation)

The formalization captures the likely structure of the proof and the fundamental errors that cause such attempts to fail, serving as an educational resource about NP vs co-NP and the challenges in proving their equivalence or separation.
