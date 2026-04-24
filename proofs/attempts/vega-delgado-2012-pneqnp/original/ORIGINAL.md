# Original Paper: P versus UP

**Author:** Frank Vega Delgado
**Year:** 2012 (February)
**Title:** P versus UP
**Claim:** P ≠ NP
**Woeginger's List:** Entry #83
**Publication:** IEEE Latin America Transactions (partial/variant); arXiv (withdrawn)
**Source:** arXiv:1205.3655v4 (withdrawn)
**Blog:** http://the-point-of-view-of-frank.blogspot.com/

---

## Abstract

The paper claims to prove that P ≠ NP by assuming P = UP and deriving a contradiction. The argument is that if P = UP, then EXP = P, which contradicts the Time Hierarchy Theorem (EXP ≠ P). Therefore, P ≠ UP. Since UP ⊆ NP, this is claimed to imply P ≠ NP.

---

## Core Argument

### Complexity Classes Involved

- **P**: Decision problems solvable in deterministic polynomial time.
- **UP (Unambiguous Polynomial time)**: NP problems where any accepting computation path is unique (if it exists). UP is also called "Unambiguous NP."
- **NP**: Decision problems verifiable in polynomial time (or solvable by nondeterministic polynomial-time Turing machines).
- **EXP (EXPTIME)**: Decision problems solvable in deterministic exponential time (2^poly(n)).

### Known Relations

- P ⊆ UP ⊆ NP ⊆ EXP
- EXP ≠ P (Time Hierarchy Theorem, Hartmanis & Stearns, 1965)
- The relationship between P and UP, and between UP and NP, are open problems.

### The Claimed Proof Steps

**Step 1 (Assumption):** Assume P = UP.

**Step 2 (Derivation):** From P = UP, derive that EXP = P.

> The paper claims that if P = UP (i.e., unambiguous nondeterminism adds no power over determinism at the polynomial level), then this collapses must "propagate upward" to collapse EXP into P as well. The specific mechanism cited involves the existence of one-way functions and properties of unambiguous computation.

**Step 3 (Contradiction):** EXP = P contradicts the Time Hierarchy Theorem (which proves EXP ≠ P).

**Step 4 (Conclusion):** By reductio ad absurdum, P = UP is false, hence P ≠ UP.

**Step 5 (Final Claim):** Since UP ⊆ NP and P ≠ UP, therefore P ≠ NP.

---

## Publication History

- The paper "The existence of one-way functions" was available at Frank Vega Delgado's blog: http://the-point-of-view-of-frank.blogspot.com/
- A variant appeared under the title "P versus UP" in the IEEE Latin America Transactions.
- A version was submitted to arXiv under the pseudonym "Asia Furones" and was subsequently withdrawn by arXiv administrators for violating arXiv's policy against pseudonyms.
- The proof has not been accepted by the complexity theory community.

---

## Related Work by the Same Author

Frank Vega Delgado submitted multiple papers over the years with different and sometimes contradictory conclusions regarding P vs NP. See also:
- The November 2010 attempt (#68 on Woeginger's list) — a different approach.
- The June 2015 attempt — claiming P = NP via the "equivalent-P" class.
- The February 2016 attempt — claiming P = NP implies P = EXP.

---

## References

- Woeginger's P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #83)
- Time Hierarchy Theorem: Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms." Transactions of the American Mathematical Society.
- UP complexity class: Valiant, L. G. (1976). "Relative complexity of checking and evaluating." Information Processing Letters.
