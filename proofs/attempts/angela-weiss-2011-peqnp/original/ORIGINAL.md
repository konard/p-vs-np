# Original Paper: A Polynomial Algorithm for 3-sat

**Author:** M. Angela Weiss
**Year:** 2011 (Spring)
**Institution:** Instituto de Matemática e Estatística, Universidade de São Paulo (IME/USP)
**URL:** http://www.ime.usp.br/~weiss/
**Woeginger's List:** Entry #74 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

---

*Note: The main paper "A Polynomial Algorithm for 3-sat" (P=NP.pdf) is no longer accessible
on the author's website (HTTP 404). The ORIGINAL.pdf file in this directory contains
"exemplo1.pdf" — Example 1 ("A simple pivoted sat") from the author's website, which
demonstrates the basic tableau technique used in the approach. The content below is
reconstructed from:*
*1. Woeginger's list description (entry #74)*
*2. The author's website at IME/USP (http://www.ime.usp.br/~weiss/)*
*3. The examples available on the website (exemplo1.pdf through exemplogame6.pdf)*
*4. The methodology described in the Woeginger listing*

---

## Abstract (Reconstructed from Available Sources)

The paper claims to demonstrate that P = NP by presenting a deterministic polynomial-time
algorithm for the 3-satisfiability problem (3-SAT). The methodology employs classical
KE-tableaux techniques to construct a "macro" that preserves pertinent data — specifically
all closed branches — within a tableau framework applied to any given 3-SAT formula.

The author works at the Instituto de Matemática e Estatística (IME) of the Universidade
de São Paulo (USP), Brazil, and the paper was made available through the author's
institutional website in Spring 2011.

---

## Background: KE-Tableaux

The paper builds upon the KE-tableau system (also known as KE calculus), introduced by
D'Agostino and Mondadori (1994). KE-tableaux extend standard analytic tableaux with
the **KE rule** (also called the "cut rule" or "principle of bivalence"):

```
     φ
    / \
   T   F
```

For any formula φ, one can branch on φ being true or false, regardless of whether φ
is a subformula of the formula being analyzed. This distinguishes KE-tableaux from
Smullyan-style analytic tableaux, where branching is restricted to subformulas.

The KE rule corresponds to the classical law of excluded middle: for any proposition P,
either P is true or P is false (P ∨ ¬P).

---

## Core Methodology (Reconstructed)

### 1. Setting Up the 3-SAT Instance

Given a 3-SAT formula:
```
φ = C₁ ∧ C₂ ∧ ... ∧ Cₘ
```

where each clause Cᵢ contains at most 3 literals over variables x₁, x₂, ..., xₙ.

### 2. KE-Tableau Application

Apply a KE-tableau to determine the satisfiability of ¬φ (to check if φ is unsatisfiable):

- **Alpha rules**: Decompose conjunctions
  - From T(A ∧ B): branch to T(A) and T(B) on the same branch
- **Beta rules**: Decompose disjunctions
  - From T(A ∨ B): branch to T(A) or T(B) on separate branches
- **KE rule**: Split on any formula P
  - Create two branches: one where T(P) holds, one where F(P) holds

### 3. The "Macro" Construction

The central innovation claimed in the paper is the construction of a **macro** structure:

- A macro is a compressed representation of the tableau's branching structure
- The macro is claimed to encode all "closed branches" (branches that lead to
  contradictions, i.e., both T(L) and F(L) for some literal L) without explicitly
  enumerating all 2ⁿ possible variable assignments
- By tracking which combinations of variable assignments lead to closed branches,
  the macro supposedly allows reconstruction of whether the entire tableau closes
  (formula is unsatisfiable) or has an open branch (formula is satisfiable)

### 4. Polynomial-Time Claim

The paper claims that:
- The macro can be constructed in polynomial time O(nᵏ) for some fixed k
- Evaluating the macro on a given 3-SAT formula takes polynomial time
- Therefore, 3-SAT ∈ P

### 5. P = NP Conclusion

Since 3-SAT is NP-complete (Cook 1971), a polynomial-time algorithm for 3-SAT implies
every problem in NP is in P, hence P = NP.

---

## Examples Referenced on the Author's Website

The author's website (http://www.ime.usp.br/~weiss/) contains several examples:

1. **"A simple pivoted sat"** (exemplo1.pdf): A simple 3-SAT instance demonstrating
   the basic tableau approach
2. **"A 3-Sat into a game"** (exemplogame2-1.pdf): An example showing 3-SAT as a game
3. **"A 3-Sat and its closed intervals"** (exemplogame2-2.pdf): The interval/closed
   branch approach
4. **"Linearized version"** (exemplogame2-3.pdf): "A closed digraph turned into a
   Linearized digraph" — showing how the branching structure is linearized
5. **Additional example** (exemplogame6.pdf): Further illustration

The website also mentions:
- **"P=NP and my failure proof"** (pnp.html): A note suggesting the author later
  recognized limitations in the approach
- **"Timeline"** (Timeline.txt): A chronological overview of the research

---

## Author's Note on Failure

The presence of a page titled "P=NP and my failure proof" on the author's website
suggests that the author may have later recognized issues with the claimed proof.
This is consistent with the pattern of the work not being accepted by peer-reviewed
venues and not appearing in standard academic databases.

---

## Key Mathematical Claims in the Paper

### Claim 1: Macro Existence
> There exists a macro M(φ) for any 3-SAT formula φ such that:
> - M(φ) encodes all closed branches of the KE-tableau for ¬φ
> - |M(φ)| is bounded by a polynomial in |φ|

### Claim 2: Macro Construction
> The macro M(φ) can be constructed in polynomial time from φ.

### Claim 3: Macro Evaluation
> Evaluating M(φ) to determine whether ¬φ is a tautology (equivalently, whether φ
> is unsatisfiable) takes polynomial time.

### Claim 4: Correctness
> φ is satisfiable if and only if the KE-tableau for ¬φ is not closed, which is
> equivalent to M(φ) indicating an open branch.

---

## Where the Argument Breaks Down

The proof fails at **Claim 1** and **Claim 2**: the macro's size and construction time.

The fundamental issue is that for worst-case 3-SAT instances (e.g., random 3-SAT near
the phase transition at clause-to-variable ratio ≈ 4.267), the tableau necessarily has
exponentially many branches. Compressing this structure requires either:

1. Storing exponential information (contradicting polynomial size), or
2. Losing information needed to correctly determine satisfiability, or
3. Using a genuinely novel insight that eliminates exponential branching — but no such
   insight is provided or verified

The KE cut rule, while powerful, does not in itself reduce worst-case complexity from
exponential to polynomial. This was shown by Ben-Sasson and Wigderson (1999) in the
closely related context of resolution proof systems.

---

## References in Paper (Reconstructed)

1. D'Agostino, M., Mondadori, M. (1994). "The Taming of the Cut: Classical Refutations
   with Analytic Cut." *Journal of Logic and Computation*, 4(3), 285–319.

2. Cook, S.A. (1971). "The complexity of theorem proving procedures."
   *STOC 1971*, 151–158.

3. Smullyan, R. (1968). *First-Order Logic*. Springer-Verlag.

---

*This reconstruction is based on publicly available descriptions of the paper from
Woeginger's list and the author's website. The original PDF was not accessible through
standard web fetching at the time of this formalization.*
