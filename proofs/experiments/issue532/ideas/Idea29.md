# Idea 29 — Reduction chains and polynomial composition

**Verdict:** Correct tool, insufficient alone (general theorem proved)

Polynomial-time many-one (Karp) reductions compose. With the repository's explicit polynomials `⟨coefficient, degree⟩`, where `eval n = coefficient · (n+1)^degree`, both addition and substitution are closed. For substitution, the proved bound is `q(p(n)) ≤ (q.c·(p.c+1)^{q.k}) · (n+1)^{p.k·q.k}`. As a result, the running time, output size and correctness of a chain "`f` then `g`" are again polynomially bounded and correct, and polynomial-time decidability transfers backwards along reductions. That makes the tool sound, but it only moves hardness around. The theorem `reducesToP_iff_inP` shows that "reduce `L` to some problem in P" is *equivalent* to "`L` is in P". So any argument of the form "reduce NP to something easy" still owes a genuine reduction, and for an NP-complete `L` (with an honest machine model and Cook–Levin, both cited, not formalized) supplying it is equivalent to proving P = NP.

## 1. The idea at full strength

Research-log item 29 records the idea as "Reduction chain to SAT: preservation and target correctness compose". The obligation it names is to "formalize an actual NP-complete reduction, input encodings, and polynomial time bounds for each composition".

Issue #532, Part I, item 7 ("NP-hardness and P vs NP") says that NP-hardness "tells us **where structure fails**" and that "Negative knowledge is progress". Every NP-hardness statement is a claim about a chain of reductions. Part II, Phase 1 asks for complexity classes "with explicit encodings" and "explicit resource bounds", and Phase 3 asks to prove "NP-hardness precisely". The machinery behind all of these is what this idea formalizes: reductions compose, and their costs compose polynomially.

At full strength there are two hopes:

* **Towards P = NP:** find a chain `SAT → L₁ → … → M` that ends at a problem `M` which is already known to be polynomial-time, and compose it with `M`'s algorithm.
* **Towards P ≠ NP:** use the closure of P under reductions to transfer a lower bound from one problem to every NP-complete problem.

## 2. Precise mathematical formulation

* `Poly = ⟨coefficient, degree⟩`, with `eval p n = coefficient · (n+1)^degree`. This has the same field names as `Complexity.Polynomial` in `proofs/complexity`.
* `Poly.add p q = ⟨p.c + q.c, max p.k q.k⟩`.
* `Poly.comp p q = ⟨q.c · (p.c+1)^{q.k}, p.k · q.k⟩`, the bound for "`q` after `p`".
* `IsReduction f L M :≡ ∀ x, L x ↔ M (f x)`.
* `PolyMap sa sb` bundles:
  * a map `fn : α → β`;
  * an abstract cost function `time : α → ℕ`;
  * polynomials `timeBound` and `sizeBound` with `time x ≤ timeBound(sa x)` and `sb (fn x) ≤ sizeBound(sa x)`.
  
  Here `sa`, `sb` are size functions (for example, the bit length of the encoding).
* `PolyReduction sa sb L M` is a `PolyMap` whose `fn` is an `IsReduction`.
* `PolyDecider sa L` bundles a Boolean `decide` with a cost function and a polynomial time bound, and requires `L x ↔ decide x = true`. `InP sa L :≡ Nonempty (PolyDecider sa L)`.
* `ReducesToP sa L :≡ ∃ β sb M, Nonempty (PolyReduction sa sb L M) ∧ InP sb M`.

The cost of running `f` then `g` on input `x` is `f.time x + g.time (f.fn x)`. This is the standard sequential cost; writing out and reading back the intermediate result is already counted in the two cost functions.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `Poly.eval_mono` / `eval_mono` | Explicit polynomials are monotone | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `Poly.add_bound` / `add_bound` | `p(n) + q(n) ≤ (p.add q)(n)` for all `n` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `Poly.comp_bound` / `comp_bound` | `q(p(n)) ≤ (p.comp q)(n)` for all `n` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `poly_add_exists`, `poly_comp_exists` | Existential closure forms | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `IsReduction.comp` / `reduction_comp` | `f : L ≤ M`, `g : M ≤ N` ⇒ `g ∘ f : L ≤ N` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyMap.comp` / `polymap_comp` | Composition of bounded maps is bounded (explicit bounds) | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `comp_time_poly` | Time of `f` then `g` is polynomial in the input size | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyReduction.comp` / `polyred_comp` | Polynomial reductions compose | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyReduction.comp_fn` / `polyred_comp_fn` | The composite computes `g ∘ f` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyDecider.pullback` / `pullback` | Decider for `M` + reduction `L ≤ M` ⇒ decider for `L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inP_of_reduction` | `L ≤ M`, `M ∈ P` ⇒ `L ∈ P` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inP_closed` | `InP` is closed backwards under reductions | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `closed_contains_family` | A closed class containing a complete language contains the family | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `reducesToP_iff_inP` | `ReducesToP L ↔ InP L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |

Lean and Rocq use the same names except for the namespaced Lean forms (`Poly.x`, `IsReduction.comp`, `PolyMap.comp`, `PolyReduction.comp`, `PolyDecider.pullback`), which are `x`, `reduction_comp`, `polymap_comp`, `polyred_comp` and `pullback` in Rocq. All proofs are general: they quantify over all types, size functions, languages, maps and cost functions.

## 4. Complete argument

**Addition.** Let `D = max(p.k, q.k)`. Because `n+1 ≥ 1`, we have `(n+1)^{p.k} ≤ (n+1)^D` and `(n+1)^{q.k} ≤ (n+1)^D`. So `p.c(n+1)^{p.k} + q.c(n+1)^{q.k} ≤ (p.c+q.c)(n+1)^D`.

**Substitution.** Write `X = (n+1)^{p.k} ≥ 1`. Then:

* `p(n) + 1 = p.c·X + 1 ≤ p.c·X + X = (p.c+1)·X`.
* Raising both sides to the power `q.k` (monotone): `(p(n)+1)^{q.k} ≤ (p.c+1)^{q.k} · X^{q.k} = (p.c+1)^{q.k} · (n+1)^{p.k·q.k}`.
* Multiplying by `q.c` gives `q(p(n)) ≤ (p.comp q)(n)`.

The `+1` inside `eval` is what makes this simple: it keeps `X ≥ 1`, so the constant term is absorbed.

**Composed maps.** Given `f : PolyMap sa sb` and `g : PolyMap sb sc`, the size of the composite output is:

`sc(g(f x)) ≤ g.size(sb(f x)) ≤ g.size(f.size(sa x)) ≤ (f.size.comp g.size)(sa x)`.

The middle step uses monotonicity. For time:

`f.time x + g.time(f x) ≤ f.time(sa x) + g.time(f.size(sa x)) ≤ (f.time.add (f.size.comp g.time))(sa x)`.

The size bound on `f`'s output is essential. Without it, `g` might run on an exponentially long intermediate string.

**Correctness.** `L x ↔ M (f x) ↔ N (g (f x))`.

**Closure of P.** A decider for `M` pulled back along `f` has cost `f.time x + d.time (f x)`, which is handled as above. Its correctness is the transitivity chain.

**Obligation equivalence.**

* (⇒) is the closure of P.
* (⇐) uses the identity reduction `L ≤ L`. It has zero cost and size bound `n ≤ 1·(n+1)^1`.

So "`L` reduces to something in P" carries *no* information beyond "`L ∈ P`".

## 5. Known results and literature

* R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer Computations*, Plenum, 1972. Polynomial-time many-one reductions, their transitivity, and 21 NP-complete problems.
* S. A. Cook, "The complexity of theorem-proving procedures", STOC 1971. NP-completeness of SAT, stated for polynomial-time Turing reductions.
* L. A. Levin, "Universal sequential search problems", *Problems of Information Transmission*, 1973 (Russian original). Independent discovery of NP-completeness.
* Standard textbook facts (for example Arora–Barak, *Computational Complexity: A Modern Approach*, 2009): P is closed under polynomial-time many-one reductions; if any NP-complete problem is in P then P = NP.

Not formalized here: any concrete NP-complete reduction (Cook–Levin), a machine model with real step counts, or a string encoding. The cost function is abstract, and the theorems hold for *every* cost function that meets the stated bounds. Idea 28 formalizes one concrete reduction (Tseitin, formula-SAT ≤ 3-SAT) together with its size bounds.

## 6. How far the idea can be pushed toward P vs NP

The open obligation is stated as a definition, not assumed:

```lean
def ReducesToP {α : Type} (sa : α → Nat) (L : α → Prop) : Prop :=
  ∃ (β : Type) (sb : β → Nat) (M : β → Prop),
    Nonempty (PolyReduction sa sb L M) ∧ InP sb M
```

By `reducesToP_iff_inP`, `ReducesToP sa SAT` is equivalent to `InP sa SAT`. The only content a "reduce NP to P" argument can add is the explicit reduction and the explicit decider. Both must satisfy:

1. **Correctness on every input.** `IsReduction` quantifies over *all* `x`, not typical ones.
2. **Polynomial time *and* polynomial output size.** The latter is used in `PolyMap.comp`.
3. **A polynomial decider for the target.** This must be a real one, not a decider that is only correct on the image of `f`, and not one with a hidden exponential cost.

In the other direction, `closed_contains_family` shows that a P ≠ NP proof via reductions needs *one* lower bound for one NP-complete problem, and closure spreads it. The reductions themselves carry no lower-bound information. Barriers: reductions relativize (they work in every oracle world), so any separation obtained purely by reduction bookkeeping would contradict Baker–Gill–Solovay 1975. The substance has to come from elsewhere.

## 7. Failure modes this idea catches

* **Invalid or non-preserving reductions** (error family 4 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). `IsReduction` is an `↔` for every input. One-directional maps, or maps that are only correct on "nice" inputs, do not compose into deciders.
* **Hidden exponential work** (error family 2). `PolyMap.comp` needs the output-size bound. A reduction that is fast per output bit but produces an exponentially long output breaks the time bound of the next stage.
* **Reductions in the wrong direction** (error family 4). Reducing an easy problem *to* SAT proves nothing about SAT. `inP_of_reduction` transfers membership in P only from target to source.
* **Circular reasoning** (error family 12). `reducesToP_iff_inP` shows that an argument whose key step is "SAT reduces to an easy problem" assumes its conclusion unless both the reduction and the decider are explicit.
* **Encoding-size mistakes** (error family 17). The size functions `sa`, `sb` are explicit. Changing the encoding (for example unary numbers) changes what "polynomial" means.
* **Solving a different problem** (error family 5). A decider correct only on a promise does not compose. See Idea 32 for the formal counterexample and the promise version of this composition.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea29.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea29.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
