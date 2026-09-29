# Original Proof Attempt: Ari Blinder (2009)

**Title:** "A Possible New Approach to Resolving Open Problems in Computer Science"

**Author:** Ari Blinder

**Date:** December 2009

**Claim:** P ≠ NP

**Status:** Retracted by author on March 10, 2010

**Original Source:** http://sites.google.com/site/ariblindercswork/ (No longer publicly accessible)

**Listed on:** [Woeginger's P versus NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), Entry #58

---

## Note on Original Document

The original paper by Ari Blinder is **not publicly accessible**. The author's website at http://sites.google.com/site/ariblindercswork/ requires authentication and the paper was never published in academic venues after the author's retraction.

## Available Information from Woeginger's List

From Woeginger's P vs NP page (Entry #58):

> **Ari Blinder**, December 2009
>
> "A Possible New Approach to Resolving Open Problems in Computer Science"
>
> The author claims to have proved that P is not equal to NP. He demonstrates the existence of a language contained in NP but not in co-NP, which establishes that NP ≠ co-NP and therefore P ≠ NP.
>
> **Update (March 10, 2010):** The author announced he had discovered a flaw in his proof.

---

## Reconstructed Proof Idea

Based on the description from Woeginger's list and standard approaches to this strategy, Blinder's proof attempt likely followed this structure:

### Core Strategy

**Objective:** Prove P ≠ NP by demonstrating NP ≠ co-NP

**Logical Foundation:**
1. **Known Fact:** P is closed under complement (if L ∈ P, then L̄ ∈ P)
2. **Known Fact:** P ⊆ NP and P ⊆ co-NP
3. **Known Fact:** If P = NP, then NP = co-NP (by closure under complement)
4. **Contrapositive:** If NP ≠ co-NP, then P ≠ NP

### Proposed Approach

To prove NP ≠ co-NP, Blinder attempted to:

1. **Construct** a specific language L
2. **Prove** L ∈ NP (show polynomial-time verification exists)
3. **Prove** L̄ ∉ NP (show no polynomial-time verifier exists for the complement)
4. **Conclude** L ∈ NP \ co-NP, establishing NP ≠ co-NP
5. **Therefore** P ≠ NP

### Anticipated Steps (Standard for This Approach)

#### Step 1: Language Construction
- Define a language L with specific properties
- Ensure L has polynomial-time verification
- Design L so its complement appears difficult to verify

#### Step 2: Prove L ∈ NP
- Provide a polynomial-time verifier V for L
- Show that for all x ∈ L, there exists a certificate c verifiable in polynomial time
- Demonstrate the verifier's correctness and polynomial time bound

#### Step 3: Prove L̄ ∉ NP (Critical Step)
- Show that no polynomial-time verifier exists for L̄
- This requires proving a **universal negative** statement
- Must demonstrate impossibility of verification for all possible verifiers

#### Step 4: Conclude NP ≠ co-NP
- From L ∈ NP and L̄ ∉ NP, conclude NP ≠ co-NP
- Use the contrapositive relationship

#### Step 5: Derive P ≠ NP
- Apply the known result: (NP ≠ co-NP) → (P ≠ NP)

---

## Why This Approach Faces Fundamental Difficulties

### 1. Universal Negative Problem

Proving L̄ ∉ NP requires showing:
- **∀V ∀t:** (PolynomialTime(t) → ¬(V correctly verifies L̄ in time t))

This is an extremely strong statement requiring:
- Consideration of all possible verifiers (infinite)
- Proof that none can work
- No known general techniques for such proofs

### 2. Relativization Barrier

Baker-Gill-Solovay (1975) showed:
- There exist oracles A where NP^A = co-NP^A
- There exist oracles B where NP^B ≠ co-NP^B
- Standard proof techniques cannot separate these classes
- Any relativizing proof would work for both oracles (contradiction)

### 3. Natural Proofs Barrier

Razborov-Rudich (1997) limitations:
- "Natural" proof methods cannot prove circuit lower bounds
- These lower bounds are needed for NP ≠ co-NP
- Constructive, widely applicable techniques face this barrier

### 4. Circular Reasoning Risk

Common pitfalls in such approaches:
- Assuming properties of L that implicitly require NP ≠ co-NP
- Using complexity assumptions equivalent to the conclusion
- Not establishing properties from first principles

### 5. Equivalence in Difficulty

Proving NP ≠ co-NP is **nearly as hard** as proving P ≠ NP:
- Both face the same fundamental barriers
- Both require non-relativizing techniques
- Both need to overcome natural proofs barrier
- No known separation technique for one that doesn't apply to the other

---

## Author's Retraction

On **March 10, 2010**, Ari Blinder publicly announced:
- He had discovered a **critical flaw** in his proof
- The proof was **invalid**
- The paper was **retracted**

The specific technical details of the flaw were not publicly documented, but likely involved one or more of:
- Gap in proving L̄ ∉ NP
- Circular reasoning in the argument
- Implicit assumption equivalent to NP ≠ co-NP
- Missing formal justification for a critical step
- Failure to account for proof barriers

---

## Scientific Value

Despite being incorrect, this attempt demonstrates:

### Positive Aspects
1. ✅ **Scientific Integrity:** Blinder's willingness to retract shows proper scientific practice
2. ✅ **Valid Strategy:** The approach is theoretically sound if NP ≠ co-NP could be proven
3. ✅ **Understanding:** Shows deep knowledge of complexity class relationships
4. ✅ **Educational:** Illustrates why certain proof strategies fail

### Lessons Learned
1. 📚 Complexity class separation faces fundamental barriers
2. 📚 Universal negative statements are extremely difficult to prove
3. 📚 Intuitive arguments require complete formal verification
4. 📚 Barrier awareness is essential for valid proof attempts
5. 📚 Self-correction is a crucial part of mathematical research

---

## References

1. Woeginger, G. J. "The P-versus-NP page" (Entry #58)
   - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

2. Baker, T., Gill, J., Solovay, R. (1975)
   - "Relativizations of the P=?NP Question"
   - SIAM Journal on Computing, 4(4), 431-442

3. Razborov, A., Rudich, S. (1997)
   - "Natural Proofs"
   - Journal of Computer Science and System Sciences, 55(1), 24-35

4. Arora, S., Barak, B. (2009)
   - "Computational Complexity: A Modern Approach"
   - Cambridge University Press

---

## Translation Note

The original paper was in English. Since the original document is not publicly accessible, this reconstruction is based on:
- Woeginger's list description
- Standard approaches to NP vs co-NP separation
- Known barriers to complexity class separation
- Common patterns in failed proof attempts

A complete formal analysis would require access to the original paper, which is no longer available.
