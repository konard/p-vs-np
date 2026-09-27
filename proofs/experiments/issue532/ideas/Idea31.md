# Idea 31 — Length-wise advice (truth-table circuits)

**Verdict:** Refuted as a route (general theorem)

As a *non-uniform* tool, length-wise advice is correct and fully general. For every `n` and every Boolean function `f`, the complete decision tree `build n f` (a table lookup, or multiplexer) computes `f` on all `n`-bit inputs (`build_correct`). The tree has exactly `2^n` leaves and `2^(n+1) − 1` nodes. Its leaves are the truth table, so the advice for length `n` is exactly `2^n` bits and determines `f` on that length. No shorter fixed advice length handles every function (`no_shorter_advice`).

As a *route to a uniform polynomial-time algorithm*, the idea is refuted in general, for two reasons.

1. **Size.** The advice is exponential. Even parity, which is in P, needs a decision tree with `2^n` leaves (`parity_tree_leaves`).
2. **Uniformity.** Advice can encode anything. Every length-only language has one-bit advice, i.e. a one-node tree at every length. For *every* enumeration of uniform deciders, some such language is decided by none of them (`advice_beyond_uniform`).

So a family of small objects, one per length, is not an algorithm. Closing the gap is exactly the obligation `UniformPolyAdvice`. Meeting it amounts to giving a uniform algorithm (`uniform_advice_decides`). Nothing here decides P vs NP.

## 1. The idea at full strength

Research-log item 31 says: "Length-wise advice ... a two-entry table stores any one-bit-input function". The obligation it names is: "Bound advice for every input length and distinguish a family of circuits from one uniformly constructible algorithm."

Issue #532 names this directly.

* Part II, Phase 5 lists "Non-uniform advice" among the alternative models.
* Phase 1 asks for "Boolean circuits (size + depth)" and the classes "P, NP, coNP, P/poly, NC, AC⁰" "with explicit encodings / explicit resource bounds", and says: "Prove equivalences **explicitly**, not by folklore".
* Part I, item 5 stresses that "Model choice matters".

At full strength, the idea reads: "for each input length, store (or build) a lookup structure for SAT; since each length is a finite problem, SAT is 'solved' for every `n`." The general question is how much advice this needs, and when advice can be replaced by a uniform algorithm. The theorems below answer both questions for all `n`, not just for the one-bit toy of the research log.

## 2. Precise mathematical formulation

* Decision trees: `DTree ::= leaf b | node lo hi`. `eval (node lo hi) (b :: x)` follows `hi` if `b = true` and `lo` otherwise. `eval (node _ _) [] = false`. `leaves` and `size` (all nodes) are the usual counts. `leafList` lists the leaves from left to right.
* `build 0 f = leaf (f [])`. `build (n+1) f = node (build n (f ∘ (false ::))) (build n (f ∘ (true ::)))`.
* `allBool n`: all `n`-bit inputs, `false`-prefixed first.
* Advice: `advice n f = leafList (build n f)`. Decoding: `ofTable n t` splits `t` into halves of length `2^(n−1)` and recurses.
* Parity: `parity [] = false`, `parity (b :: x) = b xor parity x`.
* Polynomials: `p(n) = c·(n+1)^k`.
* The obligation, with the uniform class `Uniform` kept as a parameter:

```lean
def UniformPolyAdvice (Uniform : (Nat → List Bool) → Prop) (L : List Bool → Bool) : Prop :=
  ∃ (gen : Nat → List Bool) (decode : List Bool → List Bool → Bool) (p : Poly),
    Uniform gen ∧ (∀ n, (gen n).length ≤ p.eval n) ∧
    ∀ x, decode (gen x.length) x = L x
```

This is the standard class P/poly (advice of polynomial length, one string per input length), with the additional requirement that the advice itself is generated uniformly.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `build_correct` | For all `n`, `f`: the table-lookup tree computes `f` on length `n` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `build_leaves` | `build n f` has exactly `2^n` leaves | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `build_size` | `size (build n f) + 1 = 2^(n+1)` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `allBool_length`, `mem_allBool`, `allBool_nodup` | `2^n` distinct inputs, exactly those of length `n` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `build_leafList` | The leaves of `build n f` are the truth table of `f` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `advice_length` | The advice for length `n` is exactly `2^n` bits | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `ofTable_advice` | Decoding the advice gives back the tree | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `advice_injective` | Equal advice ⇒ equal functions on length `n` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `table_of_ofTable` | Every table of length `2^n` is realized by `ofTable n` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `cover_length` | Pigeonhole for covered duplicate-free lists | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `no_shorter_advice` | For `m < 2^n` and any decoder, some `f` defeats all advice strings of length `m` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `parity_tree_leaves` | Any tree computing `c xor parity` on length `n` has `≥ 2^n` leaves | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `parity_tree_exact` | The bound is attained by `build n parity` | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `unary_one_bit` | Length-only languages have a one-node tree at each length | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `advice_beyond_uniform` | Every enumeration of deciders misses some one-bit-advice language | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |
| `uniform_advice_decides` | The obligation unpacks into a single uniform decider | [Idea31.lean](../lean/Idea31.lean) | [Idea31.v](../rocq/Idea31.v) |

In Rocq, `DTree.eval` is named `teval`, and `leaves`, `size`, `leafList` are plain functions. Helper lemmas are shared by both files (`nodup_map_cons`, `leaves_pos`). The Rocq file additionally proves `nodup_app_intro`, `firstn_app_exact`, `skipn_app_exact`, `uncovered_or_cover` and `differ_or_agree`. The last two are constructive case splits, which Lean handles with `Classical.byContradiction` (core Lean, no added declarations).

## 4. Complete argument

**Correctness and size of the table lookup.** Induct on `n` with `f` generalized. For `n = 0`, the only input is `[]`. For `n + 1`, the first bit selects the subtree built for `f ∘ (b ::)`, and the induction hypothesis applies to the tail. Leaves satisfy `L(n+1) = 2·L(n)`, and nodes satisfy `S(n+1) = 2·S(n) + 1`. This gives `2^n` and `2^(n+1) − 1`.

**Advice is the truth table.** `leafList (build (n+1) f)` concatenates the leaf lists of the two subtrees. `allBool (n+1)` lists the `false`-prefixed inputs first and then the `true`-prefixed ones. So by induction `leafList (build n f) = map f (allBool n)`, which has length `2^n`. `ofTable` splits the table at `2^n` and recurses, so it inverts `advice`. Since `build n f` computes `f`, equal advice gives equal functions on length `n`.

**No shorter advice.** Fix `m < 2^n` and any decoder `decode : advice → input → bit`. Map every advice string `a` of length `m` to its table `map (decode a) (allBool n)`. There are `2^m < 2^(2^n)` such strings but `2^(2^n)` distinct tables. By pigeonhole (`cover_length`), some table `t` is hit by no advice string. Let `f = eval (ofTable n t)`. By `table_of_ofTable`, the table of `f` is `t`. If some `a` agreed with `f` on all of `allBool n`, the table of `a` would be `t`, a contradiction. So for every `a` there is an input of length `n` where `decode a` and `f` differ.

**Parity needs every leaf.** Induct on `n`, keeping a general polarity `c`. A leaf cannot compute `c xor parity` on length `n + 1`, because the inputs `false :: 0ⁿ` and `true :: 0ⁿ` have different parity. For a node, the `lo` subtree computes `c xor parity` on length `n` and the `hi` subtree computes `(¬c) xor parity`. By induction each has `≥ 2^n` leaves, so the node has `≥ 2^(n+1)`. Parity is trivially computable in linear time. So the exponential size of the table lookup is intrinsic to the *representation*, not to the problem: decision trees read every bit along a path and cannot reuse work.

**Advice beyond uniform algorithms.** Let `e : ℕ → (input → bit)` be any enumeration, for example of all polynomial-time machines. Define `u n = ¬ e n (0ⁿ)` and `L x = u |x|`. At every length, `L` is constant, so a single leaf computes it (`unary_one_bit`). But `L (0ⁱ) = ¬ e i (0ⁱ)`, so `e i ≠ L` for every `i`. Since the enumeration is arbitrary, no countable family of uniform algorithms captures one-bit advice. In particular, P/1 is not contained in P. Taking `e` to enumerate all Turing machines, it contains undecidable languages as well.

**The obligation is the whole problem.** `uniform_advice_decides` shows that the combined map `x ↦ decode (gen |x|) x` is itself a decider. When `gen` is uniform and polynomial-time, this is a uniform polynomial-time algorithm. Advice therefore gives no leverage toward P vs NP beyond the uniform algorithm it hides.

## 5. Known results and literature

* R. M. Karp, R. J. Lipton, "Some connections between nonuniform and uniform complexity classes", STOC 1980. Introduced advice classes such as P/poly. It also shows that if NP ⊆ P/poly, the polynomial hierarchy collapses to its second level.
* The fact that P/1 contains undecidable (unary) languages is standard textbook material (e.g. Arora–Barak, *Computational Complexity: A Modern Approach*, 2009, Ch. 6). The diagonal argument above is the core of it.
* P/poly equals the class of languages with polynomial-size circuit families. Formalizing this equivalence, and P ⊆ P/poly, is outside this file (see Idea 30).
* C. E. Shannon (1949) and O. B. Lupanov (1958): most functions need circuits of size about `2^n/n`, and every function has circuits of that size. Only the decision-tree analogue (`2^n` leaves, and the advice pigeonhole) is formalized here. Circuit-size asymptotics are not formalized.
* L. Adleman (1978): BPP ⊆ P/poly. This shows that advice can absorb randomness. Not formalized.

## 6. How far the idea can be pushed toward P vs NP

The open obligation:

```lean
def UniformPolyAdvice (Uniform : (Nat → List Bool) → Prop) (L : List Bool → Bool) : Prop :=
  ∃ (gen : Nat → List Bool) (decode : List Bool → List Bool → Bool) (p : Poly),
    Uniform gen ∧ (∀ n, (gen n).length ≤ p.eval n) ∧
    ∀ x, decode (gen x.length) x = L x
```

For `L = SAT`, with `Uniform` the polynomial-time generators and `decode` polynomial time, this is exactly P = NP. Without the `Uniform` clause, it is NP ⊆ P/poly. That is believed false, since it would collapse PH (Karp–Lipton), but it is open. The theorems here show that the route gives no leverage.

* The naive advice (the truth table) is `2^n` bits, and `no_shorter_advice` shows that no uniform compression works for *all* functions. Any polynomial advice for SAT must exploit SAT's structure. That structure is exactly what a direct algorithm would exploit.
* `advice_beyond_uniform` shows that "small at every length" does not imply "computable". A per-length construction must come with a single uniform generator, otherwise it proves nothing about P.

Barriers. A proof of NP ⊄ P/poly would be a superpolynomial circuit lower bound. It faces the natural-proofs barrier (Razborov–Rudich 1997) and is not provable by relativizing techniques alone (Baker–Gill–Solovay 1975). See Idea 30.

Relation to other ideas: Idea 19 (uniform vs non-uniform) and Idea 30 (circuit lower bounds by counting; this file gives the matching table-lookup *upper* bound in the decision-tree model).

## 7. Failure modes this idea catches

* **Uniformity/non-uniformity confusion** (error family 16 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). "SAT has a finite table at each length, so SAT is easy" confuses a family with an algorithm (`advice_beyond_uniform`).
* **Hidden exponential work** (error family 2). The table lookup is `2^n` in size, even for parity (`parity_tree_leaves`).
* **Counting mistakes** (error family 7). Advice shorter than `2^n` cannot serve every function (`no_shorter_advice`). Claims of a universal compression scheme fail this count.
* **Encoding size** (error family 17). The advice is part of the input size budget. A "polynomial" algorithm that reads an exponential table is not polynomial in `n`.
* **Diagonalization misuse** (error family 13). The diagonal argument here is legitimate but only separates uniform classes from advice classes. It says nothing about P vs NP.
* **Special or easier problem** (error family 5). Unary languages are trivially compressible. Success on them does not transfer to SAT.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea31.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea31.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
