# Ruijia Liao (2011) - P≠NP via 3SAT_N and Cantor Diagonalization

**Attempt ID**: 71 (from Woeginger's list)
**Author**: Ruijia Liao
**Year**: 2011 (submitted January 11, 2011; last revised November 11, 2013)
**Claim**: P ≠ NP
**Paper**: "The Complexity of 3SAT_N and the P versus NP Problem"
**Source**: http://arxiv.org/abs/1101.2018
**Status**: ❌ **REFUTED** - Contains fundamental errors in the diagonalization argument

---

## Directory Structure

- `README.md` - Overview of the attempt and error analysis
- `original/` - Original paper materials and English reconstruction
  - `README.md` - Summary of the original paper and reconstruction links
  - `ORIGINAL.md` - English reconstruction of arXiv:1101.2018
  - `ORIGINAL.pdf` - Original arXiv draft
- `proof/` - Forward formalization of the claimed argument
- `refutation/` - Formalization of the failure in the diagonal argument

Root-level `ORIGINAL.md` and `ORIGINAL.pdf` files are kept as compatibility copies.

---

## Summary

Liao introduces a variant of 3SAT called **3SAT_N** (normal expressions), extends Tovey's classification theorem to this variant, and then introduces **aggressive truth assignments** as a tool to study polynomial-time solvability. Using a metric space structure on truth assignments and Cantor's diagonal argument, Liao attempts to show that if a polynomial-time algorithm for 3SAT_N exists, there must be uncountably many such algorithms — a contradiction, since algorithms are countable.

**The Fatal Flaw**: The diagonalization argument in Case (1) of Section 10 does not correctly construct a sequence outside the enumeration. The constructed sequence `{fn}` (equation 29) is claimed to not be in the enumeration (26), but the proof fails to show this under the formal definitions of equivalence used. The diagonal construction builds a sequence `{fn}` whose `k`-th element uses aggressive truth assignment `a_k` differing from `a_k^k` at position `k`, but equivalence classes are defined up to a relabeling map `π` that can equate different truth assignments. Consequently the diagonalization does not produce a genuinely new equivalence class.

---

## Main Argument

### The Setup

1. **3SAT_N** is introduced as the subproblem of 3SAT consisting of "normal" Boolean expressions: no tautological clauses, no repeated clauses, all clauses are "full" (3 distinct variables). Liao proves 3SAT_N is NP-complete (Theorem 1).

2. **Classification Theorem** (Theorem 2): Every instance of 3SAT_N with at most 3 occurrences per variable is already satisfiable; NP-hardness only arises at 4 occurrences per variable.

3. **Aggressive truth assignments** generalize ordinary truth assignments. An aggressive truth assignment `e₁e₂...eₘ` for an instance `η ∈ 3SAT_N(n)`:
   - First tries to evaluate `η` using Algorithm 1 (the standard polynomial-time truth assignment evaluator);
   - If that returns `false`, then checks whether `η ∈ ∪_{s=1}^{3}(3,s)-SAT_N(n)` (easily satisfiable by the Classification Theorem).
   - Returns `true` if either check succeeds, `false` otherwise.

4. **Pseudo-algorithms** are defined as elements of sets "compatible" with the P vs NP problem (Definition 1). The set TA₁ of all aggressive truth assignments is proved compatible (Proposition 1).

5. **Metric space** (TA∞, d): A metric is defined on the set of all finite and infinite compositions of aggressive truth assignments.

6. **Cauchy sequences and representations**: For a fixed polynomial-time algorithm `f`, the set `<f>` of all algorithms obtainable by composing `f` with aggressive truth assignments is a metric space. Regular Cauchy sequences in `<f>₂` each converge to a representation polynomial-time algorithm (Lemma 8).

### The Claimed P ≠ NP Proof (Section 10)

Assume A = {polynomial-time algorithms on ∪_{n≥3} 3SAT_N(n)} is non-empty.

**Case (1)**: Assume A_a ⊆ A for all aggressive truth assignments a. Liao argues:
- The set ECS of equivalence classes of regular Cauchy sequences would be uncountable (by a diagonal argument mimicking Cantor's proof that real numbers are uncountable).
- Each equivalence class has a unique polynomial-time algorithm representation (Lemma 8, Corollary 10).
- Therefore A contains uncountably many distinct algorithms.
- But there are only countably many algorithms. Contradiction.

**Case (2)**: Assume there exists a∗ such that A_{a∗} ⊄ A. But then f_λ a∗ is a polynomial-time algorithm (since both f_λ and a∗ run in polynomial time) and should be in A. Contradiction.

Therefore A = ∅ and P ≠ NP.

---

## The Critical Errors

### Error 1: The Diagonal Argument Does Not Work as Stated

**The core problem** lies in the diagonal construction in Case (1), Section 10.

Liao enumerates all equivalence classes as `{f^1_n}, {f^2_n}, ...` and constructs a new sequence `{f_n}` (equation 29) using diagonal aggressive truth assignments `a₁, a₂, ...` (equation 28). The claim is that `{f_n}` is not equivalent to any `{f^k_n}` in the list.

**Why it fails**: The equivalence of two sequences `{f_n} ≡ {f^k_n}` is defined (Definition 7) as: `f_{a_n} a_0 ≡ f_{a^k_n} a^k_0` under a bijective ordered map `π_n` for each `n`. Under this definition, two different truth assignments `a` and `b` can be equivalent under a map that relabels variables. Liao's argument that `{f_n} ∉ [{f^k_n}]` because `a_k` differs from `a^k_k` at one position does not account for the possibility that they could be equivalent under some non-identity relabeling map `π`.

In Proposition 2, Liao proves that *any two* elements of TA₁ are equivalent (under the appropriate map). This means that all of TA₁ forms a single equivalence class! This directly undermines the diagonalization in Case (1): the constructed sequence `{f_n}` will be equivalent to sequences already in the enumeration, because equivalence is so coarse.

### Error 2: Proposition 2 Contradicts the Diagonal Argument

**Proposition 2 states**: Any `a₁, a₂ ∈ TA₁` are equivalent.

This means there is only ONE equivalence class in TA₁. Consequently, the set `<f>₁ = {f_a | a ∈ TA₁}` has only one equivalence class as well (since all elements of TA₁ are equivalent under Proposition 2).

The diagonal construction uses distinct aggressive truth assignments to create supposedly different sequences. But if all aggressive truth assignments are equivalent, then sequences differing only in which aggressive truth assignments they use are all equivalent — defeating the attempt to construct a new equivalence class by diagonal argument.

### Error 3: The Claim "ECS is Uncountable" Is Not Properly Established

Even if we accept the diagonal construction at face value, the argument uses the structure of binary representations (equation 27-28) to mimic Cantor's diagonal proof. However:

- In Cantor's proof, the diagonal argument works because the new number differs from the n-th number at the n-th decimal digit **by value** (a specific difference: if digit n of the n-th number is 0, use 1, and vice versa).
- In Liao's construction, `a_k` is constructed to differ from `a^k_k` at position `k`. However, equivalence classes of sequences are defined using bijective relabeling maps (Definition 7). Two sequences that differ at one atomic truth assignment position might still be equivalent after relabeling. This means the constructed sequence is not guaranteed to be outside any equivalence class in the enumeration.

### Error 4: Case (2) Depends on Unclear Assumption

Case (2) assumes there exists `a∗ ∈ TA₁` such that `f_λ a∗ ∉ A`. The refutation claims this is a contradiction because `f_λ a∗` runs in polynomial time. This case (2) argument is actually correct in isolation — if we accept that A is closed under composition with aggressive truth assignments, then A must be empty. But the argument is circular: the conclusion (A = ∅) is used to derive the premises of both cases.

### Error 5: The Proof Does Not Circumvent Known Barriers

Liao claims in Section 2 that the proof avoids relativization, natural proofs, and algebrization barriers because:
- Pseudo-algorithms are explicitly described by Algorithm 1 or 2 plus Algorithm 3.
- The argument combines algorithms, pseudo-algorithms, and diagonalization.

However, the proof heavily depends on properties specific to the way 3SAT_N instances are structured. A standard relativization argument could be applied to show the proof cannot distinguish between a world with P = NP and one with P ≠ NP, indicating the proof technique relativizes and thus cannot separate the classes.

---

## What Liao Actually Showed

To be fair, the paper does establish several correct results:

✅ **3SAT_N is NP-complete** (Theorem 1) — correct reduction from 3SAT  
✅ **Classification Theorem** (Theorem 2) — correctly extends Tovey's work  
✅ **Aggressive truth assignments are pseudo-algorithms** (Proposition 1) — the construction of an exponential-time algorithm using compositions of 2^n aggressive truth assignments is valid  
✅ **The metric space structure on TA∞** (Lemma 2) — the metric construction is correct  
❌ **ECS is uncountable** — the diagonal argument is flawed because equivalence is too coarse  
❌ **P ≠ NP** — does not follow from the flawed diagonalization  

---

## Why This Approach Is Appealing

The approach is tempting because:

1. **Cantor's diagonalization IS a powerful technique**: It works for showing the reals are uncountable, Turing's halting problem is undecidable, etc.
2. **The metric space structure is elegant**: Defining distances between truth assignments and using Cauchy sequences is mathematically sophisticated.
3. **3SAT_N is a natural variant**: The normalization of SAT instances is a reasonable technical step.

However, **Cantor's diagonalization requires that the diagonal element genuinely differs from each listed element**. When equivalence classes are used instead of direct comparison, the diagonal element might fall into an existing equivalence class due to the coarseness of the equivalence relation.

---

## Broader Context

### Known Barriers to P ≠ NP Proofs

Any valid P ≠ NP proof must overcome three major barriers:

1. **Relativization Barrier** (Baker-Gill-Solovay, 1975): There exist oracles A and B such that P^A ≠ NP^A and P^B = NP^B. A proof technique that "relativizes" (works the same way regardless of oracle) cannot resolve P vs NP.

2. **Natural Proofs Barrier** (Razborov-Rudich, 1997): If pseudorandom functions exist, then "natural proof" techniques (constructive, useful) cannot separate P from NP.

3. **Algebrization Barrier** (Aaronson-Wigderson, 2008): Arithmetization-based techniques, even with extension to "algebraic oracles," cannot resolve P vs NP.

Liao claims to circumvent these barriers, but the proof technique appears to relativize: the argument depends on counting algorithms, and the counting argument would apply equally in any relativized world.

---

## References

### Primary Source
- Liao, R. (2011). "The Complexity of 3SAT_N and the P versus NP Problem." arXiv:1101.2018v4 (revised November 11, 2013).

### Related Work
- Tovey, C. A. (1984). "A simplified satisfiability problem." *Discrete Applied Mathematics* 8, 85–89.
- Cantor, G. (1874, 1890). Diagonal argument papers.
- Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P=?NP Question." *SIAM J. Comput.* 4:431–442.
- Razborov, A. A., & Rudich, S. (1997). "Natural Proofs." *J. Comput. Sys. Sci.* 55(1):24–35.
- Aaronson, S., & Wigderson, A. (2009). "Algebrization: A New Barrier in Complexity Theory." *ACM Trans. on Computing Theory* 1(1):1–54.

### Woeginger's List
- Entry #71: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Reconstruction Files
- [`original/README.md`](original/README.md) - Summary of the original paper and reconstruction links
- [`original/ORIGINAL.md`](original/ORIGINAL.md) - English reconstruction of the draft paper
- [`original/ORIGINAL.pdf`](original/ORIGINAL.pdf) - Original arXiv draft

---

**Last Updated**: 2026-04-23
**Formalization by**: AI Issue Solver (Issue #472)
