# Idea 30 — Unrestricted circuit lower bounds (transfer and counting)

**Verdict:** Developed to an open obligation (conditional theorem proved)

Two facts are proved in general.

*Transfer.* Suppose three things hold: a circuit lower bound, a simulation of fast algorithms by small circuits, and a size bound. Together they exclude a fast algorithm. Specialized to a concrete NAND circuit model, `explicit_lower_bound_separates` shows that a function in a class `InNP` with a superpolynomial circuit lower bound is computed by no fast algorithm. `InNP` and `fast` are parameters, so read with NP and polynomial time (not formalized here), an explicit NP function with such a lower bound would separate P from NP. This uses the standard simulation P ⊆ P/poly, which is taken here as a hypothesis.

*Shannon counting.* For the concrete model, the following is machine-checked for all `n, g`: if `(g+1)·((n+g)²)^g < 2^(2^n)`, then some Boolean function on `n` bits has no circuit with at most `g` NAND gates. The argument uses words, truth tables and a pigeonhole principle, all proved from scratch.

Counting is *non-explicit*. It shows that hard functions exist, but it never names one in NP. The open obligation `ExplicitNPLowerBound` is exactly the missing step. Every known approach to it runs into the natural-proofs, relativization or algebrization barriers.

## 1. The idea at full strength

Research-log item 30 says: "lower bound plus uniform simulation and size bound excludes a fast algorithm". The obligation it names is to "prove the lower bound for unrestricted circuits computing an explicit NP language and the quantitative machine-to-circuit simulation; audit known barriers".

Issue #532 lists "Boolean circuits (size + depth)" among the models of Part II, Phase 1, and "P/poly" among its classes. Phase 2 asks to formalize "Natural Proofs (Razborov–Rudich, as far as possible)" and "Known lower bounds for restricted circuits". Phase 4 lists "counting arguments" among the proof templates to encode. Part I, item 6 ("Circuits, physics, and speed of light") asks whether circuit abstractions are complete.

At full strength, the idea is the classical program for proving P ≠ NP through circuit complexity: find a function in NP that needs superpolynomially many gates. Since every polynomial-time algorithm yields polynomial-size circuits, this would give P ≠ NP (and in fact NP ⊄ P/poly).

## 2. Precise mathematical formulation

* Words. `words alph s` lists all words of length `s` over `alph`. `codesUpTo alph s` lists all words of length `≤ s`.
* Truth tables. `allBool n = words [false,true] n` is the list of all `n`-bit inputs. A truth table is an element of `allBool (2^n)`. `fnOfTable n t` is the function whose table is `t`, in the order of `allBool n`.
* Circuits. A circuit is a NAND straight-line program `C : List (ℕ × ℕ)`. Gate `(i,j)` appends `¬(wᵢ ∧ wⱼ)` to the wire list, which starts with the input `x`. The output is the last wire. `WF n C` means that gate `k` reads only wires `< n + k`. The size of `C` is its length.
* `PolySizeCircuits f :≡ ∃ p, ∀ n, ∃ C, WF n C ∧ |C| ≤ p(n) ∧ ∀ x, |x| = n → output x C = f x`.
* `SuperpolyLowerBound f :≡ ∀ p, ∃ n, ∀ C, WF n C → |C| ≤ p(n) → ∃ x, |x| = n ∧ output x C ≠ f x`.
* `ExplicitNPLowerBound InNP :≡ ∃ f, InNP f ∧ SuperpolyLowerBound f`.

Here polynomials are `p(n) = c·(n+1)^k`. `InNP` is a parameter, because this file does not fix a machine model.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `lower_bound_transfer` | Lower bound + simulation + size bound ⇒ no fast algorithm | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `words_length` | `#words of length s over m letters = m^s` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `mem_words` | `words alph s` is exactly the words of length `s` over `alph` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `words_nodup` | Words over a duplicate-free alphabet are duplicate-free | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `allBool_length`, `allBool_nodup`, `mem_allBool` | `2^n` distinct inputs, exactly those of length `n` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `tables_length` | `2^(2^n)` truth tables | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `table_of_fnOfTable` | Every table of length `2^n` is the table of a function | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `cover_length` | Pigeonhole: a duplicate-free covered list is no longer than the codes | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `uncovered_table` | `#codes < 2^(2^n)` ⇒ some table is decoded by no code | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `codesUpTo_length` | `#codes of length ≤ s ≤ (s+1)·m^s` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `shannon_codes` | Counting for any decoder from words of length `≤ s` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `shannon_circuits` | `(g+1)((n+g)²)^g < 2^(2^n)` ⇒ some `f` has no circuit of size `≤ g` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `four_bit_function_needs_three_gates` | Instance `n = 4`, `g = 2` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `superpoly_excludes_poly_circuits` | Superpolynomial lower bound ⇒ no polynomial-size circuits | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `no_fast_algorithm` | Simulation hypothesis + lower bound ⇒ no fast algorithm computes `f` | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |
| `explicit_lower_bound_separates` | `ExplicitNPLowerBound` + simulation ⇒ some `InNP` function has no fast algorithm | [Idea30.lean](../lean/Idea30.lean) | [Idea30.v](../rocq/Idea30.v) |

Helper lemmas with identical names in both files: `consAll_length`, `mem_consAll`, `nodup_map_cons`, `consAll_nodup`, `allBool_succ`, `mem_codesUpTo`, `pairsOf_length`, `mem_pairsOf`, `wf_bound`, `gateAlphabet_length`, `wf_in_alphabet`. The Rocq file additionally proves `nodup_app_intro`, `uncovered_or_cover` and `differ_or_agree`. These are constructive decidability steps that Lean handles with `Classical.byContradiction` (core Lean, no added declarations).

## 4. Complete argument

**Words.** `words alph (s+1)` prefixes each letter of `alph` to each word of `words alph s`. By induction, its length is `|alph| · m^s = m^{s+1}`. Membership is characterized exactly (length `s`, all letters in `alph`). If `alph` has no duplicates, two words produced from different first letters differ, and words with the same first letter differ in their tails. So `words` has no duplicates.

**Tables.** `allBool n` therefore has `2^n` distinct elements, and it contains exactly the lists of length `n`. There are `2^(2^n)` tables. `fnOfTable` reads the first bit, keeps the first or second half of the table, and recurses. Because `allBool (n+1)` lists the `false`-prefixed inputs first and then the `true`-prefixed ones, the table of `fnOfTable n t` is `t` itself.

**Pigeonhole.** If every table is `decode c` for some `c ∈ codes`, then the duplicate-free list of tables is a subset of `codes.map decode`. So `2^(2^n) ≤ |codes|` (`List.Nodup.length_le_of_subset` / `NoDup_incl_length`). Contrapositively, fewer codes leave a table uncovered.

**Circuits as codes.** For a well-formed circuit with `k ≤ g` gates, every gate index is `< n + k ≤ n + g` (`wf_bound`). So the circuit is a word of length `≤ g` over the alphabet `gateAlphabet n g` of `(n+g)²` pairs. Decode a circuit to its truth table `(allBool n).map (output · C)`. Counting leaves a table `t` uncovered. Take `f = fnOfTable n t`. If some circuit of size `≤ g` agreed with `f` on all inputs of length `n`, its table would equal the table of `f`, which is `t`. That is a contradiction.

**Asymptotics (not formalized).** Take `g = 2^n / (4n)`. Then `log₂((g+1)(n+g)^{2g}) ≈ 2g·n = 2^n / 2 < 2^n`. So for large `n`, some `n`-bit function needs about `2^n/(4n)` NAND gates. Shannon's bound is `2^n/n` up to constants. This file only proves the exact finite criterion and one instance.

**Transfer.** `superpoly_excludes_poly_circuits` instantiates the polynomial from `PolySizeCircuits` in the lower bound. `no_fast_algorithm` composes this with the simulation hypothesis. `explicit_lower_bound_separates` just unpacks the obligation.

## 5. Known results and literature

* C. E. Shannon, "The synthesis of two-terminal switching circuits", *Bell System Technical Journal* 28 (1949). Counting shows that most functions need exponentially large circuits.
* O. B. Lupanov (1958). Every function on `n` bits has circuits of size `(1+o(1))·2^n/n`, so the counting bound is tight up to lower-order terms.
* P ⊆ P/poly (polynomial-time machines have polynomial-size circuit families). Savage 1972; Pippenger–Fischer 1979 (size `O(t log t)`). Not formalized here, and taken as the `simulation` hypothesis.
* T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP question", *SIAM J. Comput.* 1975.
* A. Razborov, S. Rudich, "Natural proofs", *JCSS* 1997. If strong enough pseudorandom functions exist, no "natural" (constructive and large) property proves superpolynomial circuit lower bounds.
* S. Aaronson, A. Wigderson, "Algebrization: a new barrier in complexity theory", *ACM TOCT* 2009.
* Restricted models, where lower bounds *are* known:
  * AC⁰: Ajtai 1983; Furst–Saxe–Sipser 1984; Håstad 1986.
  * Monotone circuits: Razborov 1985.
  * AC⁰[p]: Razborov 1987; Smolensky 1987.
  * NEXP ⊄ ACC⁰: Williams 2011.
* Best explicit lower bounds for unrestricted circuits over the full binary basis are only linear: about `3.1·n`. See Find–Golovnev–Hirsch–Kulikov (FOCS 2016, `(3 + 1/86)n`) and Li–Yang (STOC 2022, `3.1n − o(n)`).

None of these results is formalized here except the counting core.

## 6. How far the idea can be pushed toward P vs NP

```lean
def ExplicitNPLowerBound (InNP : (List Bool → Bool) → Prop) : Prop :=
  ∃ f, InNP f ∧ SuperpolyLowerBound f
```

With the simulation hypothesis, `explicit_lower_bound_separates` turns this obligation into a separation. What is missing:

1. **Explicitness.** Counting gives `∃ f` for each input length, non-constructively. It does not place any hard function in NP. The gap between "most functions are hard" and "*this* NP function is hard" is the whole problem.
2. **Barriers.**
   * *Natural proofs.* The counting property "has no small circuit" is large (most functions have it). A lower-bound proof that uses a large, efficiently checkable property cannot work if pseudorandom functions exist (Razborov–Rudich). The pigeonhole argument above is the prototype of a large property. It escapes the barrier only because it is non-constructive, and for the same reason it cannot name a function.
   * *Relativization.* Pure simulation/diagonalization arguments relativize (Baker–Gill–Solovay), so they cannot settle P vs NP.
   * *Algebrization.* Arithmetization-based techniques do not suffice either (Aaronson–Wigderson).
3. **The quantitative simulation** (machine steps to circuit gates) must also be formalized to turn the conditional theorem into an unconditional one.

Relation to the other ideas:

* Idea 31 gives the matching *upper* bound: every function has a table-lookup circuit of size about `2^n`.
* Idea 19 covers the uniform/non-uniform gap.
* Idea 28 covers the proof-complexity analogue, where the obligation is a lower bound for extended resolution instead of for circuits.

## 7. Failure modes this idea catches

* **Assuming a lower bound** (error family 1 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). `explicit_lower_bound_separates` makes the lower bound an explicit premise. It cannot be slipped in as "clearly SAT needs large circuits".
* **Counting mistakes** (error family 7). Counting proves existence, not hardness of a given function. The precise inequality `(g+1)((n+g)²)^g < 2^(2^n)` must hold, and it fails for small `n` relative to `g`.
* **Ignoring barriers** (error family 14). Arguments of the same shape as `uncovered_table`, when made constructive, are natural proofs.
* **Uniformity mismatches** (error family 16). A circuit lower bound is non-uniform. Transferring it to algorithms needs the P ⊆ P/poly simulation, which is a separate theorem. In the other direction, small circuits for each length do not give an algorithm (Idea 31).
* **Restricted-model results mistaken for general ones** (error family 5). Lower bounds for AC⁰ or monotone circuits do not apply to `Circuit` here, which is unrestricted NAND.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea30.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea30.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
