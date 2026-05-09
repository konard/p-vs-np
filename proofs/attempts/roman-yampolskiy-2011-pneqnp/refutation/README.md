# Refutation: Yampolskiy 2011 - Why HPTSP ∉ P is Not Proven

**Navigation:** [↑ Back to Attempt Root](../README.md)

---

## Purpose

This directory contains the **formal refutation** of Yampolskiy's claimed proof that HPTSP ∉ P. We identify and formalize each logical error in the paper, demonstrating that the argument is insufficient to establish P ≠ NP.

**Important:** This refutation does NOT claim HPTSP ∈ P. The complexity status of HPTSP remains unknown. We only show that Yampolskiy's specific argument fails.

---

## Files

| File | Description |
|------|-------------|
| `lean/YampolskiyRefutation.lean` | Lean 4 formalization of all identified errors |
| `rocq/YampolskiyRefutation.v` | Rocq (Coq) formalization of all identified errors |

---

## Summary of Errors

### Error 1: Unproven Cryptographic Assumptions

**Paper's Claim:** Hash functions like SHA-1 satisfy the Strict Avalanche Criterion (SAC): each output bit changes with probability 50% when any single input bit is flipped.

**Why It Fails:**
- SAC is a *statistical/heuristic* property, not a mathematical theorem.
- It cannot be expressed as a deterministic mathematical property of all hash functions.
- SHA-1 specifically has known collision vulnerabilities (Wang et al., CRYPTO 2005).
- Even if true for specific functions, it is not provable from any formal axioms.

**Formal consequence:** In the proof assistants, this can only be expressed as an unjustified axiom (not a derivable theorem).

---

### Error 2: Hash Computational Irreducibility

**Paper's Claim:** Knowing the hash of a partial path provides no information about the hash of the complete path.

**Why It Fails:**
- This is an informal intuition, not a formal mathematical statement.
- Without a probabilistic or information-theoretic framework (which the paper doesn't provide), it cannot be formalized.
- Even if formalized, it would require the probabilistic version, which doesn't directly imply computational hardness.

**Formal consequence:** Can only be axiomatized, not proven.

---

### Error 3: Non-Sequitur: "No Pruning → Exponential Time"

**Paper's Claim:** Since no pruning is possible (due to hash properties), any algorithm must examine all V! Hamiltonian cycles, requiring exponential time.

**Why It Fails (the central flaw):**
- "No pruning-based algorithm works" ≠ "no polynomial-time algorithm exists."
- Pruning is one algorithmic paradigm among many. Polynomial-time algorithms can work via:
  - Dynamic programming (no pruning needed)
  - Linear programming / ellipsoid method
  - Randomized algorithms
  - Algebraic methods exploiting problem structure
  - Algorithms exploiting the specific hash construction
- **Analogy:** Finding the maximum element of a list "requires examining all elements," but it's still O(n) time, not exponential.

**Formal consequence:** The implication "no pruning → must check all paths → exponential" cannot be proven. We can only derive trivial consequences from the premise.

---

### Error 4: Flawed Compression Argument

**Paper's Claim:** Computing the optimal HPTSP solution without examining all paths would be equivalent to compressing a random string, which is impossible.

**Why It Fails:**
1. Not all HPTSP instances have random edge costs — the argument only applies to specific instances.
2. Incompressibility (Kolmogorov complexity) is an information-theoretic property, not a computational one.
3. You *can* compute many properties of incompressible strings in polynomial time:
   - Sum of characters: O(n)
   - Count of a specific character: O(n)
   - Maximum character: O(n)
   - Any fixed-size hash of the string: O(n)
4. The connection between the incompressibility of random strings and HPTSP hardness is never formally established.

**Formal consequence:** We demonstrate by example that computing properties of "random-looking" data is still polynomial.

---

### Error 5: No Standard Lower Bound Technique

**Paper's Claim:** Provides an exponential lower bound for HPTSP.

**Why It Fails:**
Any valid proof that a problem is outside P must use standard techniques:
- Reduction from a known NP-hard problem (Cook's theorem style)
- Diagonalization argument (as in the proof of the time hierarchy theorem)
- Circuit complexity lower bounds (like for monotone circuits)
- Communication complexity arguments
- Geometric arguments

The paper uses **none** of these. It relies entirely on informal intuition about hash functions.

---

### Error 6: Circular Reasoning with Ladner's Theorem

**Paper's Claim:** "As a consequence, via Ladner's theorem, we show that NPI is non-empty."

**Why It Fails:**
- **Ladner's Theorem (1975):** *IF* P ≠ NP, *THEN* NPI ≠ ∅.
- The theorem has P ≠ NP as a **hypothesis** (input), not a conclusion.
- Yampolskiy attempts to:
  1. Prove P ≠ NP (via HPTSP ∉ P).
  2. Apply Ladner's theorem to conclude NPI ≠ ∅.
  3. Use "HPTSP ∈ NPI" as further evidence.
- This is **circular**: step 2 already assumes P ≠ NP!
- Additionally, showing HPTSP ∈ NPI would require proving HPTSP is not NP-complete, which is never established.

---

## What Would Be Needed for a Valid Proof

To legitimately prove HPTSP ∉ P, one would need at minimum:

1. **Formal definition of the hash function's properties** using a rigorous mathematical framework (e.g., random oracle model, or specific algebraic properties).
2. **Reduction from a known NP-complete problem** to HPTSP, establishing NP-completeness, OR
3. **Proof that HPTSP is NP-intermediate** by showing (a) HPTSP ∈ NP, (b) HPTSP is not NP-complete, and (c) HPTSP ∉ P — where (b) and (c) each require rigorous proofs.
4. Any of these would require either: proving P ≠ NP first (circular), or developing entirely new techniques.

The challenge is that proving P ≠ NP is believed to require overcoming the **relativization barrier** (Baker-Gill-Solovay 1975), **natural proofs barrier** (Razborov-Rudich 1997), and **algebrization barrier** (Aaronson-Wigderson 2008). Yampolskiy's approach addresses none of these.

---

## Educational Value

This refutation demonstrates a common pattern in failed P ≠ NP attempts:

1. Construct a problem that "obviously" cannot be solved efficiently.
2. Argue informally why it's hard.
3. Claim this proves P ≠ NP.

The gap between "obviously hard" and "provably hard" is precisely what makes P vs NP a Millennium Prize Problem. Formal verification (like the formalization in this directory) makes this gap explicit and undeniable.
