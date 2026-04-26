# Angela Weiss (2011) - P=NP via Polynomial Algorithm for 3-SAT using KE-Tableaux

**Attempt ID**: 74 (from Woeginger's list)
**Author**: M. Angela Weiss
**Year**: 2011 (Spring)
**Claim**: P = NP
**Status**: Refuted

## Directory Structure

- `README.md` - Overview of the attempt and error analysis
- `original/` - Original source material and English reconstruction
  - `README.md` - Short summary of the original proof idea
  - `ORIGINAL.md` - English reconstruction of the draft paper
  - `ORIGINAL.pdf` - Closest available original source from the author's website
- `proof/` - Forward formalization of the claimed argument
- `refutation/` - Formal refutation and gap analysis

## Summary

In Spring 2011, M. Angela Weiss (University of São Paulo, IME/USP) proposed a polynomial-time
algorithm for the 3-satisfiability problem (3-SAT), claiming to prove P = NP. The approach
employs KE-tableaux (a classical proof method in propositional logic) to construct a
"macro" structure that purportedly preserves all closed branches of a tableau applied to any
3-SAT formula, thereby reducing the search space to polynomial size.

## Main Argument

### The Approach

1. **KE-Tableaux Foundation**: KE-tableaux (also called "KE calculus" or cut-based tableaux)
   are a complete tableau method for propositional logic developed by D'Agostino and Mondadori.
   Unlike standard analytic tableaux, KE-tableaux include a "cut rule" (the KE rule, based on
   the principle of bivalence) that allows case splitting on any formula without requiring it
   to be a subformula of the current branch.

2. **Tableau for 3-SAT**: Given a 3-SAT formula φ with clauses C₁ ∧ C₂ ∧ ... ∧ Cₙ, a
   tableau procedure attempts to determine satisfiability by systematically splitting on
   literals and propagating constraints. A closed branch (all branches closed) certifies
   unsatisfiability; an open branch certifies satisfiability.

3. **The "Macro" Construction**: Weiss claims to construct a "macro" — a compressed
   representation that captures all essential branching information (all closed branches)
   from the tableau. The key claim is that this macro can be built and evaluated in
   polynomial time, avoiding the exponential blowup that normally arises from the
   2ⁿ possible variable assignments.

4. **Polynomial-Time Claim**: By systematically applying the KE macro to any 3-SAT formula,
   the algorithm purportedly decides satisfiability in polynomial time in the number of
   variables and clauses.

5. **P=NP Conclusion**: Since 3-SAT is NP-complete, a polynomial-time algorithm for it
   would imply P = NP.

### Key Technical Claim

The crucial (and flawed) claim is:
- The "macro" structure compresses the tableau in such a way that all relevant branching
  information is preserved in polynomial space
- The KE rule enables linking closed branches through a fixed polynomial procedure
- No exponential enumeration of variable assignments is needed

## The Error

### Fundamental Flaw: Hidden Exponential Enumeration

**The Error**: The construction of the KE-tableau macro does not avoid exponential blowup —
it merely relocates the exponential computation into the macro's construction or evaluation.

**Why This Matters**:
- The number of branches in a tableau for an n-variable 3-SAT formula is bounded by 2ⁿ
  in the worst case
- Compressing a structure that contains exponentially many branches does not reduce its
  information content to polynomial size — the macro itself must implicitly encode
  exponential information
- The KE rule (cut rule) allows case splitting on arbitrary formulas, which does not
  reduce the number of cases that must be checked

### The Critical Distinction

#### What KE-Tableaux Can Do:
- Provide a complete proof system for propositional logic
- Potentially reduce the number of proof steps compared to standard tableaux
- Handle tautology checking efficiently for specific formula classes

#### What KE-Tableaux Cannot Do (Without Exponential Resources):
- Avoid the exponential branching inherent in worst-case 3-SAT instances
- Compress the full branching structure into polynomial space in general
- Determine satisfiability of arbitrary 3-SAT instances in polynomial time

### The Subproblem Structure

**Tableau decision procedure**:
- Worst case: 2ⁿ leaf nodes (one per complete variable assignment)
- Even with KE cuts, cannot reduce this exponential search space in the worst case
- Any compression that preserves all "closed branch" information must encode at least
  as much information as the original exponential structure

### The Unproven Assumption

The paper's critical unproven assumption:
> "The macro preserves all pertinent data (all closed branches) and can be constructed and
> evaluated in polynomial time."

**Reality**: No such polynomial construction exists unless P = NP, which is precisely
what the paper is trying to prove. The claim is circular: it assumes the hardness can be
compressed polynomially, which is exactly the P vs NP question.

### Why the Approach Is Tempting

- Tableaux are sound and complete for propositional logic
- KE-tableaux are known to be polynomially bounded for Horn clause formulas and other
  special cases
- The "macro" abstraction looks like it might avoid enumeration
- The connection between tableaux and resolution makes it plausible that structural
  insights could help

However, for worst-case 3-SAT instances with balanced clauses and no unit propagation
shortcuts, no polynomial procedure is believed to exist (unless P = NP).

## Broader Context

### Completeness vs. Efficiency

A proof system being "complete" (able to prove any tautology) does not mean it is
"efficient" (able to prove all tautologies in polynomial steps). There are complete
proof systems that require exponentially long proofs for certain tautologies.

### Tableau Methods and 3-SAT

Standard DPLL algorithms — which are closely related to tableaux — require exponential
time in the worst case for 3-SAT. Adding a cut rule (as in KE-tableaux) does not change
the worst-case complexity, as it has been shown that no polynomial-size refutation system
exists for 3-SAT unless P = NP.

### Connection to Cook's Theorem

Cook's theorem (1971) established 3-SAT as NP-complete. Any claimed polynomial-time
algorithm for 3-SAT must either:
1. Have a subtle flaw in its complexity analysis (as in Weiss's case), or
2. Actually prove P = NP — which no peer-reviewed proof has yet accomplished

## Formalization Goals

In this directory, we formalize:

1. **3-SAT Problem Definition**: The formal structure of 3-SAT instances
2. **KE-Tableau System**: The tableau rules including the KE (cut) rule
3. **Weiss's Claimed Algorithm**: Formalization of the macro construction approach
4. **The Error**: Where the polynomial-time claim breaks down
5. **Refutation**: Why no polynomial-time algorithm can solve 3-SAT unless P = NP

The formalization demonstrates that:
- KE-tableaux are a sound and complete proof system
- The claimed macro construction does not provide a polynomial-time decision procedure
- The polynomial-time claim contains a hidden exponential complexity

## References

### Primary Sources

- **Original Claim**: Weiss, M.A. (2011). "A Polynomial Algorithm for 3-sat"
  - Available at: http://www.ime.usp.br/~weiss/
  - Institution: Instituto de Matemática e Estatística, Universidade de São Paulo (IME/USP)
  - Spring 2011
- **Original reconstruction**: [`original/README.md`](original/README.md), [`original/ORIGINAL.md`](original/ORIGINAL.md), [`original/ORIGINAL.pdf`](original/ORIGINAL.pdf)

### Context

- **Woeginger's List**: Entry #74
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Related to issue**: #44 (general P vs NP tracking)

### Background on KE-Tableaux

- D'Agostino, M., Mondadori, M. (1994). "The Taming of the Cut: Classical Refutations
  with Analytic Cut." *Journal of Logic and Computation*, 4(3), 285–319.
- D'Agostino, M. (1992). "Are Tableaux an Improvement on Truth-Tables?"
  *Journal of Logic, Language and Information*, 1(3), 235–252.

### Background on 3-SAT Complexity

- **Cook, S.A.** (1971). "The complexity of theorem proving procedures."
  *Proceedings of the 3rd Annual ACM Symposium on Theory of Computing*, 151–158.
  (Established 3-SAT as NP-complete)
- **Ben-Sasson, E., Wigderson, A.** (1999). "Short Proofs Are Narrow — Resolution Made
  Simple." *Proceedings of STOC 1999*.
  (Shows connection between proof size and width in resolution, related to tableau complexity)

## Key Insights

### Why P ≠ NP Is Plausible

This attempt illustrates a common pattern in P=NP claims:
- A complete proof procedure (tableaux) is used
- A structural optimization (macros/compression) is claimed to eliminate exponential search
- The claimed optimization either shifts the exponential work or assumes what it tries to prove
- Peer review finds the hidden exponential complexity

### The "Compression" Fallacy

Many P=NP attempts follow this pattern:
1. Take an exponential procedure (tableau, SAT solver, etc.)
2. Propose a "compressed" representation
3. Claim the compression is polynomial in size
4. Fail to prove the compression is actually polynomial (or prove it incorrectly)

The compression fallacy is seductive because many NP problems admit polynomial witnesses
for YES instances (making them in NP), but finding such witnesses efficiently is the hard part.

## See Also

- [P vs NP Overview](../../../README.md) - Overview of the P vs NP problem
- [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) - Complete list of attempts
