# Ruijia Liao (2011) - Refutation

## Why the Proof Fails

Liao's 2011 P≠NP attempt contains a fundamental flaw in the Cantor diagonalization argument in Section 10: **the diagonal construction does not produce a sequence outside all equivalence classes, because Proposition 2 (proven in Section 7 of the same paper) makes all aggressive truth assignments equivalent**.

---

## The Fatal Error: Self-Defeating Equivalence Relation

### The Claim

Section 10 attempts to show that if polynomial-time algorithms for 3SAT_N exist, there are uncountably many such algorithms — a contradiction since algorithms are countable. The argument uses Cantor's diagonal method.

### The Problem

**Proposition 2 (Section 7, proven by Liao himself)**: Any two aggressive truth assignments `a₁, a₂ ∈ TA₁` are equivalent.

This means TA₁ has **exactly one equivalence class** under the relation defined in Definition 5.

The diagonal argument in Section 10 (Case 1) constructs a new sequence {f_n} by choosing aggressive truth assignments `a_k` that differ from the k-th enumerated sequence's `a^k_k` at position k. But since all elements of TA₁ are equivalent (Proposition 2), any `a_k` is equivalent to any `a^k_k` under some relabeling map π. Under Definition 7, which defines equivalence of sequences using the same relabeling map, the sequence {f_n} will be equivalent to sequences already in the enumeration.

### The Contradiction Within the Paper

The proof has two incompatible results:

| Result | Location | Statement |
|--------|----------|-----------|
| **Proposition 2** | Section 7 | Any `a₁, a₂ ∈ TA₁` are equivalent — only ONE equivalence class in TA₁ |
| **Section 10 Diagonal** | Section 10 | Constructs a sequence not equivalent to any enumerated class — requires MANY equivalence classes |

If TA₁ has only one equivalence class, then all sequences built from TA₁ elements are equivalent to each other, making the diagonal construction trivially fail.

---

## Technical Analysis of the Error

### Step-by-Step Breakdown

**Step 1**: Proposition 2 establishes that for any `a₁, a₂ ∈ TA₁`, there exists an ordered bijection `π` such that for any η:
- `a₁(η)` and `a₂(π(η))` have the same implementation sequences.

This means `a₁ ≡ a₂` for ALL pairs. TA₁ is a single equivalence class.

**Step 2**: The diagonal construction (equation 28) defines `a_k` to differ from `a^k_k` at position k (the k-th atomic truth assignment). Specifically:
- `a^k_k = e^k_1 e^k_2 ... e^k_k ...`
- `a_k = ¬e^1_1 ¬e^2_2 ... ¬e^k_k e_{k+1} ¬x*_{k+2} ...`

**Step 3**: But by Proposition 2, `a_k ≡ a^k_k` under some relabeling map `π_k`.

**Step 4**: Under Definition 7, sequence equivalence means `f_{a_n a_0} ≡ f_{a^k_n a^k_0}` under some bijective ordered map for each n. By Proposition 2, such maps exist because any two aggressive truth assignments are equivalent.

**Step 5**: Therefore {f_n} = {f_{a_n a_0}} IS equivalent to some sequence in the enumeration. The claimed contradiction dissolves.

---

## Why Cantor's Diagonal Doesn't Apply Here

Cantor's diagonal argument works when the items being diagonalized over have **fine-grained identity**: a real number is uniquely characterized by all its decimal digits, and changing a single digit produces a genuinely different number.

Liao's setup uses an **equivalence relation** that is too coarse:

- **Real numbers**: Two numbers are equal iff ALL digits are equal. Changing one digit gives a new number.
- **Liao's sequences**: Two sequences are equivalent if there EXISTS a bijective relabeling map under which they have the same implementation. This allows different sequences to be "the same" under renaming.

The diagonal construction produces a sequence with different aggressive truth assignments, but since all aggressive truth assignments are equivalent (Proposition 2), the different assignments don't produce a genuinely new equivalence class.

---

## Additional Issues

### Issue 1: Circular Structure of the Proof

The proof assumes A ≠ ∅ (polynomial-time algorithms for 3SAT_N exist) and derives two cases:
- Case (1): A is closed under composition with aggressive truth assignments → contradiction via diagonalization
- Case (2): A is not closed → f_λ a∗ is polynomial-time but claimed not in A → contradiction

Case (2) is arguably correct in isolation. However, it depends on the definition of A being the set of ALL polynomial-time algorithms, which would trivially include f_λ a∗ since a∗ is polynomial time. This case alone would suffice to show A = ∅ IF we interpret A as exactly those algorithms... but this circular.

### Issue 2: The Representation Lemma

Lemma 8 claims that every regular Cauchy sequence {f_n} has a polynomial-time algorithm representation f_ζ (defined in equation 23 as f_ζ(η) = f_{n-2}(η) for η ∈ 3SAT_N(n)).

This definition of f_ζ is well-defined only if the base algorithm f is already polynomial-time (which is the assumption A ≠ ∅). The claim that f_ζ is polynomial-time because "it takes fewer steps than f_{ã₀ã₀}" (Lemma 7) is an efficiency comparison, not a standalone polynomial-time guarantee. The argument is circular.

### Issue 3: Barriers Not Circumvented

Liao claims the proof circumvents relativization, natural proofs, and algebrization barriers by using pseudo-algorithms that are "different from any oracle and arithmetization."

However, the proof's core argument is about counting algorithms — specifically, that there would be uncountably many polynomial-time algorithms. This counting argument would apply equally in any relativized world (where oracle access is added), because:
1. The set A (polynomial-time algorithms) becomes oracle-dependent.
2. In a world where P^oracle = NP^oracle, A might be non-empty.
3. The diagonal construction would still produce the same alleged contradiction.

Since the argument gives the same result regardless of oracle, it relativizes, and by the Baker-Gill-Solovay result, it cannot resolve P vs NP.

---

## What Liao Actually Proved

To be fair, these results in the paper are correct:

- ✅ **3SAT_N is NP-complete** (Theorem 1)
- ✅ **Classification Theorem** (Theorem 2) — extends Tovey's work correctly
- ✅ **(TA∞, d) is a metric space** (Lemma 2)
- ✅ **Proposition 2: All elements of TA₁ are equivalent** — but this undermines the diagonalization
- ✅ **Proposition 3: TA_m has infinitely many equivalence classes for m ≥ 2** — but the diagonalization uses sequences in <f>₂, and the relevant equivalence is between sequences (Definition 7), not elements of TA_m

---

## The Core Lesson

Cantor's diagonalization is a powerful method, but it requires that the "identity" of objects be preserved under the operations being performed. When objects are grouped into equivalence classes, the diagonal argument must produce a class genuinely distinct from all enumerated classes — not just an object whose "raw form" differs at one position, but whose equivalence class has not been seen before.

In Liao's setup, the equivalence relation on sequences is defined so broadly (via relabeling maps over all of TA₁) that virtually all sequences using elements of TA₁ become equivalent. The diagonal fails to escape the equivalence classes.

---

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`prop2_undermines_diagonal`**: Proposition 2 implies the diagonal construction fails.
2. **`diagonal_sequence_not_new`**: The constructed diagonal sequence is equivalent to some enumerated sequence.
3. **`ECS_not_uncountable`**: The uncountability claim cannot be derived from the axioms.

---

## References

- **Liao, R.** (2011). "The Complexity of 3SAT_N and the P versus NP Problem." arXiv:1101.2018v4.
- **Baker, T., Gill, J., & Solovay, R.** (1975). "Relativizations of the P=?NP Question." *SIAM J. Comput.* 4:431–442.
- **Cantor, G.** (1890). Diagonal argument (Über eine Elementare Frage der Mannigfaltigkeitslehre).
- **Tovey, C. A.** (1984). "A simplified satisfiability problem." *Discrete Appl. Math.* 8, 85–89.
- **Woeginger's List**: Entry #71 — https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Related Files

- [`../original/README.md`](../original/README.md) - Original paper materials and reconstruction summary
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - English reconstruction of the draft paper
- [`../original/ORIGINAL.pdf`](../original/ORIGINAL.pdf) - Original arXiv draft
