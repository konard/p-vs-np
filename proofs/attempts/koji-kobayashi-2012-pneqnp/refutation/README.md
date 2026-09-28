# Kobayashi (2012) — Refutation

## Why the Proof Fails

Kobayashi's 2012 P≠NP attempt contains a fundamental logical error: **confusing representation complexity with computational complexity**.

## The Fatal Error: Reduction Size ≠ Decision Complexity

### What Kobayashi Claims (Theorem 19 → Theorem 20)

1. RCNF is P-complete (equivalent to HornCNF in log-space)
2. Some CNF formulas M_k (CCNF) require super-polynomial RCNF representation
3. Therefore: CNF cannot be polynomially reduced to RCNF ≡ HornCNF
4. **Conclusion**: P ≠ NP

### Why Step 4 Does Not Follow from Steps 1–3

The critical flaw is in the final step. Even if:

> "Some CNF formulas cannot be efficiently transformed into RCNF/HornCNF form"

This does **not** imply:

> "SAT (deciding CNF satisfiability) cannot be solved in polynomial time"

The reason: there are infinitely many ways to decide a problem. Showing that **one specific approach** (reduction to RCNF) is insufficient does not rule out all other polynomial-time algorithms.

### The Missing Bridge

To prove P ≠ NP from Kobayashi's result, one would need:

**Claim X**: Every polynomial-time algorithm for SAT must work by reducing the input to RCNF.

**Claim X is false**: Polynomial-time algorithms for HornSAT, 2-SAT, and other restricted cases do not reduce to RCNF. More importantly, if P = NP, the polynomial-time algorithm for SAT would not necessarily use RCNF at all.

## Comparison with Related Correct Results

### What Valid Proof Complexity Results Show

Real proof complexity results (e.g., Haken 1985) show:

> "Resolution requires exponentially long proofs for certain tautologies"

This is a statement about **proof length in a specific proof system**, not about **algorithm runtime**.

### The Analogous Error in Other Domains

Consider:
- Every integer can be computed in polynomial time from its prime factors
- Some integers require super-polynomial space to write out in unary
- **Wrong conclusion**: "Computing integers requires super-polynomial time"

The "computation" doesn't have to use the unary representation.

Similarly, SAT doesn't have to use the RCNF representation.

## Technical Analysis of Each Gap

| Paper Step | Status | Issue |
|-----------|--------|-------|
| RCNF is HornCNF | Correct | ✓ By construction |
| HornCNF reduces to RCNF | Plausible | Reduction not detailed |
| TCNF is NP-complete | Plausible | Reduction from 3CNF only sketched |
| TCNF is product irreducible | Unclear | "Product reducible" not precisely defined |
| CCNF has super-poly falsifying assignments | Unproven | No proof given in paper |
| CCNF requires super-poly RCNF | Unproven | No proof connecting Thm 18 to Thm 19 |
| Super-poly RCNF implies P ≠ NP | **WRONG** | Logical error: representation ≠ decision |

## The Correct Implication Structure

What Kobayashi actually proves (if Theorem 19 is correct):

```
CCNF formulas have super-polynomial RCNF representations
    ↓
CNF ⊈_p RCNF  (no polynomial-size reduction to RCNF)
    ↓
    ≠ (WRONG STEP)
    ↓
SAT ∉ P (which would give P ≠ NP)
```

The arrow marked "WRONG STEP" is the fundamental error.

## Formal Refutation

The Lean and Rocq formalizations in this directory demonstrate:

1. **`representation_ne_decision`**: Representation size in a specific form and decision complexity are different concepts
2. **`rcnf_independence`**: The fact that RCNF requires super-polynomial size does not constrain polynomial-time algorithms that avoid RCNF
3. **`kobayashi_gap_identified`**: The precise logical gap in Kobayashi's Theorem 20

## Correct Conclusion

Kobayashi's work may correctly show that certain CNF formulas cannot be compactly represented in RCNF (HornCNF). This is a potentially interesting result about **proof complexity** or **normal form complexity**, but it does not constitute a proof of P ≠ NP.

## References

- **Kobayashi, K.** (2012). "Topological approach to solve P versus NP". arXiv:1202.1194
- **Haken, A.** (1985). "The intractability of resolution". Theoretical Computer Science
- **Cook, S. A.** (1971). "The complexity of theorem-proving procedures"
- **Woeginger's List**: Entry #78 — https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
