# Original Paper: A Proof for P =? NP Problem

**Author:** Changlin Wan, Zhongzhi Shi
**Year:** May 2010 (submitted May 17, 2010; withdrawn July 1, 2020)
**arXiv ID:** [arXiv:1005.3010](https://arxiv.org/abs/1005.3010)
**Subject Classification:** Computational Complexity (cs.CC)
**Woeginger's List:** Entry #61
**Status:** WITHDRAWN by author

---

## Abstract (from arXiv)

> We give a new and recursive definition for Turing machine, and use it to describe the Turing computable function set. We define a new class D of all decidable languages, and use the subset and reduction relations to form a partial order in class D. Then we construct a TM that can accept all the recursive languages in D. We call this TM the recursive TM, and use it to define Up, the language of the recursive TM. We discuss several useful results from these definitions and then try to prove the equality P = Up = NP.

Author's withdrawal comment: "sorry for the wild thoughts and immature article writting"

---

## Paper Summary

### Section 1: Introduction

The paper begins by attempting to provide a new definition for Turing machines based on a recursive construction. The goal is to enumerate all valid Turing machines through a recursive process.

### Section 2: Recursive Definition of Turing Machines

**Definition 2.1 (Turing Machine):** The paper provides the standard definition of a Turing Machine as a 7-tuple (Q, Σ, Γ, δ, q₀, q_accept, q_reject).

**Definition 2.2 (Valid TM Encoding):** A string is a valid TM encoding if it encodes a well-formed Turing machine.

**Claim:** The paper claims to construct a "recursive definition" for TMs that can enumerate all valid TM encodings.

**Recursive TM Sequence:** The paper attempts to construct an infinite sequence TM₁, TM₂, TM₃, ... claimed to encompass all valid Turing machines.

### Section 3: The Class D of Decidable Languages

**Definition 3.1 (Class D):** The class D is defined as the collection of all decidable languages. For any two languages L₁, L₂ in D:
- Subset relation: L₁ ⊆ L₂ if and only if L₁ is a subset of L₂
- Reduction relation: L₁ ≤ₚ L₂ if L₁ is polynomial-time reducible to L₂

The class D forms a partial order under the subset and reduction relations.

### Section 4: The Language Up

**Definition 4.1 (Language Up):** The paper defines Up as the language accepted by what it calls the "recursive TM" - essentially the union of all languages in the sequence of TMs constructed in Section 2.

Formally: Up = ∪{L(TMᵢ) : i ∈ ℕ, TMᵢ is a valid TM}

The paper claims this construction is well-defined and that Up contains all languages in D.

### Section 5: Main Claims

The paper attempts to prove:

**Claim 5.1:** P ⊆ Up
- Argument: Every language in P is accepted by some TM, which appears in the TM sequence
- Therefore the language is contained in Up

**Claim 5.2:** Up ⊆ NP
- Argument: The recursive TM can simulate any TM in the sequence in polynomial time
- (This argument is vague and hand-wavy)

**Claim 5.3 (Critical):** Up ⊆ P
- Argument: The recursive TM decides membership in Up in polynomial time
- This is the main claimed result, but no concrete algorithm or time analysis is provided

**Main Theorem:** From Claims 5.1-5.3:
- P ⊆ Up (from 5.1)
- Up ⊆ P (from 5.3)
- Therefore P = Up
- Up ⊆ NP (from 5.2)
- NP ⊆ Up (since NP is a complexity class, every NP language has a TM)
- Therefore Up = NP
- Therefore P = Up = NP, proving P = NP

### Section 6: Discussion

The paper briefly discusses implications without rigorously addressing the standard barriers to proving P vs NP.

---

## Key Claims and Definitions

1. **Recursive TM Sequence:** An enumeration TM₁, TM₂, ... of all valid Turing machines
2. **Class D:** Collection of all decidable languages with subset/reduction partial order
3. **Language Up:** Union of all languages in the TM sequence, claimed to equal the "universal" language
4. **Main Result:** P = Up = NP

---

## Notes on the Paper

- The paper uses informal language in critical places where formal proofs are required
- Several definitions are imprecise or circular
- The key claim (Up ∈ P) is asserted without proof
- The author withdrew the paper on July 1, 2020 with the comment acknowledging it contained errors

---

## Reference

Wan, C., & Shi, Z. (2010). "A Proof for P =? NP Problem." arXiv:1005.3010 [cs.CC]
URL: https://arxiv.org/abs/1005.3010
