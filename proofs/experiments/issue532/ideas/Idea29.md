# Idea 29 — Reduction chains and polynomial composition

**Verdict:** Correct tool, insufficient alone (general theorem proved)

Polynomial-time many-one (Karp) reductions compose. This is proved in the repository's shared machine model: a machine reduction (`PolyReduces`) is a finite-table machine that writes `f x` within a polynomial number of `Run` steps, and two of them compose by concatenating their tables (`computes_comp`, `polyReduces_trans`). Membership in P transfers backwards along a chain (`inP_of_chain`), and NP-hardness transfers forwards (`npHard_of_reduces`). That makes the tool sound, but it only moves hardness around. The theorem `satReducesToP_iff_inP_sat` shows that the open obligation "reduce SAT to some language in P" is *equivalent* to `InP SAT`. It yields `PEqualsNP` only under the named hypothesis `SATHard` (the hardness half of Cook–Levin, not mechanised here). So any argument of the form "reduce NP to something easy" still owes a genuine machine reduction and a genuine polynomial-time machine. The explicit-polynomial arithmetic (`Poly.comp_bound` and friends) and the earlier abstract-cost development are kept, the latter as a schema.

## 1. The idea at full strength

Research-log item 29 records the idea as "Reduction chain to SAT: preservation and target correctness compose". The obligation it names is to "formalize an actual NP-complete reduction, input encodings, and polynomial time bounds for each composition".

Issue #532, Part I, item 7 ("NP-hardness and P vs NP") says that NP-hardness "tells us **where structure fails**" and that "Negative knowledge is progress". Every NP-hardness statement is a claim about a chain of reductions. Part II, Phase 1 asks for complexity classes "with explicit encodings" and "explicit resource bounds", and Phase 3 asks to prove "NP-hardness precisely". The machinery behind all of these is what this idea formalizes: reductions compose, and their costs compose polynomially.

At full strength there are two hopes:

* **Towards P = NP:** find a chain `SAT → L₁ → … → M` that ends at a problem `M` which is already known to be polynomial-time, and compose it with `M`'s algorithm.
* **Towards P ≠ NP:** use the closure of P under reductions to transfer a lower bound from one problem to every NP-complete problem.

## 2. Precise mathematical formulation

**Machine model.** The shared model of `proofs/complexity/lean/Complexity.lean`
and `proofs/experiments/issue532/lean/Machines.lean`: `Word = List Bool`,
`Language = Word → Bool`, finite instruction tables, and `Run M c t b` counting
steps. `InP L` means one machine decides `L` on every word within one
polynomial `c·(n+1)^d`.

* `Computes m f p`: from `initial x`, machine `m` reaches, within `p(|x|)`
  steps, the state just past its table with `f x` followed by blanks on the
  tape and the head at the left end.
* `PolyReduces L L' :≡ ∃ m f p, Computes m f p ∧ ∀ x, L x = L' (f x)`. The
  output-size bound follows from the time bound (`computes_output_poly`).
* **Open obligation** (Lean `SATReducesToP`):
  `∃ L' : Language, PolyReduces SAT L' ∧ InP L'`.
* Known theorems enter only as named hypotheses of the shared layer:
  `SATHard := NPHard SAT` and `CookLevin := NPComplete SAT` (membership and
  hardness together). Neither is proved here. The membership half
  `SATInNP := InNP SAT` is proved in `SATVerifier.lean` / `SATVerifier.v`
  (`SATVerifier.satInNP`); `pNotEqualsNP_of_not_satReducesToP` still takes
  it as a premise, and `pNotEqualsNP_of_not_satReducesToP'` drops it.

**Explicit polynomials.**

* `Poly = ⟨coefficient, degree⟩`, with `eval p n = coefficient · (n+1)^degree`.
  `Poly.toPolynomial` maps it to the shared `Complexity.Polynomial`, with the
  same evaluation (`Poly.eval_toPolynomial`).
* `Poly.add p q = ⟨p.c + q.c, max p.k q.k⟩`.
* `Poly.comp p q = ⟨q.c · (p.c+1)^{q.k}, p.k · q.k⟩`, the bound for "`q` after `p`".
* `IsReduction f L M :≡ ∀ x, L x ↔ M (f x)`.

**Abstract schema (kept, not a statement about P).** `PolyMapFor sa sb`
bundles a map `fn`, a *declared* cost function `time`, and polynomials
`timeBound`, `sizeBound` with `time x ≤ timeBound(sa x)` and
`sb (fn x) ≤ sizeBound(sa x)`. `PolyReductionFor`, `PolyDeciderFor`,
`InPFor sa L :≡ Nonempty (PolyDeciderFor sa L)` and `ReducesToPFor` are built
on it. Because `time` is a field, `inPFor_every` proves `InPFor sa L` for
*every* `L` (declared time `0`), so the schema records composition constants
only. `inPFor_of_inP` instantiates it with a machine's step count.

The cost of running `f` then `g` is `f.time x + g.time (f.fn x)` in the
schema, and the sum of the two step counts for concatenated tables in the
machine model.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `Poly.eval_mono` / `eval_mono` | Explicit polynomials are monotone | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `Poly.add_bound` / `add_bound` | `p(n) + q(n) ≤ (p.add q)(n)` for all `n` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `Poly.comp_bound` / `comp_bound` | `q(p(n)) ≤ (p.comp q)(n)` for all `n` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `poly_add_exists`, `poly_comp_exists` | Existential closure forms | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `Poly.eval_toPolynomial` / `eval_toPolynomial` | `p.toPolynomial.eval n = p.eval n` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `IsReduction.comp` / `reduction_comp` | `f : L ≤ M`, `g : M ≤ N` ⇒ `g ∘ f : L ≤ N` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `computes_id` | The empty table computes the identity in zero steps | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `computes_comp` | `Computes m f p → Computes m' g p' → ∃ B, Computes (appendMachine m m') (g ∘ f) B` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `polyReduces_refl` | `PolyReduces L L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `polyReduces_trans` | `PolyReduces L M → PolyReduces M N → PolyReduces L N` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inP_of_reduces` | `PolyReduces L L' → InP L' → InP L` (shared layer) | [Machines.lean](../lean/Machines.lean) | shared `Machines.v` |
| `inP_of_chain` | `PolyReduces L M → PolyReduces M N → InP N → InP L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inP_closedUnderPolyReduces` | `InP` is closed backwards under `PolyReduces` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `npHard_of_reduces` | `NPHard K → PolyReduces K M → NPHard M` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `closed_contains_np` | A class closed under `PolyReduces` that contains an NP-hard language contains NP | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `pEqualsNP_of_npHard_inP` | `NPHard K → InP K → PEqualsNP` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `reducesToP_iff_inP` | `ReducesToP L ↔ InP L` (machine version) | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `not_forall_reducesToP` | Non-vacuity: some language (`Diag`) does not reduce to P | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `SATReducesToP` | **Open obligation**: `∃ L', PolyReduces SAT L' ∧ InP L'` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `satReducesToP_iff_inP_sat` | `SATReducesToP ↔ InP SAT` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `pEqualsNP_of_satReducesToP` | `SATHard → SATReducesToP → PEqualsNP` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `satReducesToP_iff_pEqualsNP` | `CookLevin → (SATReducesToP ↔ PEqualsNP)` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `pNotEqualsNP_of_not_satReducesToP` | `SATInNP → ¬ SATReducesToP → PNotEqualsNP` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `pNotEqualsNP_of_not_satReducesToP'` | `¬ SATReducesToP → PNotEqualsNP`, with no `SATInNP` premise (`SATInNP` is proved: `SATVerifier.satInNP`) | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `satReducesToP_of_chain` | A chain `SAT ≤ L₁ ≤ L₂` with `InP L₂` discharges the obligation | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyMapFor.comp` / `polymap_comp` | Schema: composition of bounded maps is bounded (explicit bounds) | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `comp_time_poly_for` | Schema: time of `f` then `g` is polynomial in the input size | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyReductionFor.comp` / `polyred_comp` | Schema reductions compose | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyReductionFor.comp_fn` / `polyred_comp_fn` | The composite computes `g ∘ f` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `PolyDeciderFor.pullback` / `pullback` | Schema decider for `M` + schema reduction `L ≤ M` ⇒ schema decider for `L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inPFor_of_reduction` | Schema: `L ≤ M`, `InPFor M` ⇒ `InPFor L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inPFor_closed` | Schema: `InPFor` is closed backwards under schema reductions | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `closed_contains_family_for` | Schema: a closed class containing a complete language contains the family | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `reducesToPFor_iff_inPFor` | Schema: `ReducesToPFor L ↔ InPFor L` | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inPFor_every` | Every language is `InPFor` (declared time `0`): the schema alone says nothing about P | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |
| `inPFor_of_inP` | `InP L → InPFor List.length L` (schema instantiated with the step count) | [Idea29.lean](../lean/Idea29.lean) | [Idea29.v](../rocq/Idea29.v) |

Where the Rocq name differs from the Lean name, the first column gives both
(`Lean` / `Rocq`). Rocq-specific differences: the fields of `Poly` are named
`coef`/`deg` (the shared `Polynomial` already uses `coefficient`/`degree`);
`inPFor_every` takes a decision procedure `∀ x, {L x} + {¬ L x}` as a premise,
because the Rocq file does not use classical logic to produce the `bool`
decider; `inPFor_of_inP` computes the step count with `stepCount` where Lean
uses `Classical.choose`.
Not machine-checked in either language: any concrete NP-complete reduction and the hardness half of the Cook–Levin theorem, which enters
only through the named hypotheses `SATHard` and `CookLevin`. The membership half, `SATInNP`, is proved in `SATVerifier` (`SATVerifier.satInNP`).

## 4. Complete argument

**Addition.** Let `D = max(p.k, q.k)`. Because `n+1 ≥ 1`, we have `(n+1)^{p.k} ≤ (n+1)^D` and `(n+1)^{q.k} ≤ (n+1)^D`. So `p.c(n+1)^{p.k} + q.c(n+1)^{q.k} ≤ (p.c+q.c)(n+1)^D`.

**Substitution.** Write `X = (n+1)^{p.k} ≥ 1`. Then:

* `p(n) + 1 = p.c·X + 1 ≤ p.c·X + X = (p.c+1)·X`.
* Raising both sides to the power `q.k` (monotone): `(p(n)+1)^{q.k} ≤ (p.c+1)^{q.k} · X^{q.k} = (p.c+1)^{q.k} · (n+1)^{p.k·q.k}`.
* Multiplying by `q.c` gives `q(p(n)) ≤ (p.comp q)(n)`.

The `+1` inside `eval` is what makes this simple: it keeps `X ≥ 1`, so the constant term is absorbed.

**Composed machine reductions.** Let `m` compute `f` within `p` and `m'`
compute `g` within `p'`. The concatenated table `appendMachine m m'` first
runs `m` unchanged (`reaches_append`, shared layer) and after `t₁ ≤ p(|x|)`
steps is in state `|m|` with the head at the left end and `f x` followed by
blanks on the tape. Up to trailing blanks, this is the shifted initial
configuration of `m'` on `f x` (`similar_initial`). The shifted run of `m'`
(`reaches_append_right`) transfers to it (`reaches_of_similar`) and ends,
after `t₂ ≤ p'(|f x|)` steps, past the concatenated table with `g (f x)`
followed by blanks (`blankPad_word`). The output of `m` has polynomial length
`|f x| ≤ q(|x|)` (`computes_output_poly`), so `t₁ + t₂ ≤ p(n) + p'(q(n))`, a
single polynomial (`compose_bound`). The output-size bound is essential:
without it, `m'` might run on an exponentially long intermediate string. In
the machine model the bound is automatic, because a machine writes at most
one cell per step.

**Correctness.** `L x = M (f x) = N (g (f x))`.

**Closure of P.** The shared `inP_of_reduces` concatenates the reduction
table with the decider table in the same way. `inP_of_chain` combines it with
`polyReduces_trans`.

**Obligation equivalence** (`satReducesToP_iff_inP_sat`).

* (⇒) is the closure of P.
* (⇐) uses `L' = SAT` and `polyReduces_refl` (the empty table, zero steps).

So "`SAT` reduces to something in P" carries *no* information beyond
"`SAT ∈ P`". Under `SATHard` (every NP language reduces to SAT), `InP SAT`
gives `PEqualsNP` by `inP_of_reduces`; since `SATInNP` holds (it is proved
in `SATVerifier`), `¬ InP SAT` gives `PNotEqualsNP`. The obligation is not trivially true for every language:
`not_forall_reducesToP` exhibits the diagonal language `Diag`, which is not
in P (`diag_not_inP`) and hence reduces to nothing in P.

**The schema.** The same arithmetic, with declared costs: for
`f : PolyMapFor sa sb` and `g : PolyMapFor sb sc`,
`sc(g(f x)) ≤ (f.size.comp g.size)(sa x)` and
`f.time x + g.time(f x) ≤ (f.time.add (f.size.comp g.time))(sa x)`. These
bounds are correct, but because the cost functions are declared rather than
counted, `inPFor_every` shows `InPFor` holds for every language.

## 5. Known results and literature

* R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer Computations*, Plenum, 1972. Polynomial-time many-one reductions, their transitivity, and 21 NP-complete problems.
* S. A. Cook, "The complexity of theorem-proving procedures", STOC 1971. NP-completeness of SAT, stated for polynomial-time Turing reductions.
* L. A. Levin, "Universal sequential search problems", *Problems of Information Transmission*, 1973 (Russian original). Independent discovery of NP-completeness.
* Standard textbook facts (for example Arora–Barak, *Computational Complexity: A Modern Approach*, 2009): P is closed under polynomial-time many-one reductions; if any NP-complete problem is in P then P = NP.

Not formalized here: any concrete NP-complete reduction, in particular the hardness half of the Cook–Levin theorem, which appears only as the named hypotheses `SATHard` and `CookLevin`. The membership half (`SATInNP`) is proved in `SATVerifier` (`SATVerifier.satInNP`). Idea 28 formalizes one concrete reduction (Tseitin, formula-SAT ≤ 3-SAT) together with its size bounds.

## 6. How far the idea can be pushed toward P vs NP

The open obligation is stated as a definition in the shared machine model,
not assumed:

```lean
def SATReducesToP : Prop := ∃ L' : Language, PolyReduces SAT L' ∧ InP L'
```

By `satReducesToP_iff_inP_sat` it is equivalent to `InP SAT`. It implies
`PEqualsNP` under the named hypothesis `SATHard`
(`pEqualsNP_of_satReducesToP`), and is equivalent to `PEqualsNP` under
`CookLevin` (`satReducesToP_iff_pEqualsNP`). Its negation implies
`PNotEqualsNP` with no further premise (`pNotEqualsNP_of_not_satReducesToP'`;
the unprimed version takes `SATInNP`, which is proved in `SATVerifier`).
The hypotheses `SATHard` and `CookLevin` are the hardness half and the whole
of the known Cook–Levin theorem; they are not proved here. The
only content a "reduce NP to P" argument can add is the explicit reduction
and the explicit decider (`satReducesToP_of_chain` accepts any finite chain).
Both must satisfy:

1. **Correctness on every input.** `PolyReduces` quantifies over *all*
   words, not typical ones.
2. **Polynomial step count.** A finite machine table with a polynomial bound
   on the number of `Run` steps, which also bounds the output length.
3. **A polynomial decider for the target.** It must be a real machine (`InP`),
   not a decider that is only correct on the image of `f`.

In the other direction, `closed_contains_np` shows that a P ≠ NP proof via reductions needs *one* lower bound for one NP-complete problem, and closure spreads it. The reductions themselves carry no lower-bound information. Barriers: reductions relativize (they work in every oracle world), so any separation obtained purely by reduction bookkeeping would contradict Baker–Gill–Solovay 1975. The substance has to come from elsewhere.

## 7. Failure modes this idea catches

* **Invalid or non-preserving reductions** (error family 4 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). `IsReduction` is an `↔` for every input. One-directional maps, or maps that are only correct on "nice" inputs, do not compose into deciders.
* **Hidden exponential work** (error family 2). A composed reduction needs the output-size bound. A reduction that is fast per output bit but produces an exponentially long output breaks the time bound of the next stage. In the machine model this cannot be hidden: output length is bounded by the step count (`computes_output_poly`).
* **Reductions in the wrong direction** (error family 4). Reducing an easy problem *to* SAT proves nothing about SAT. `inP_of_reduces` transfers membership in P only from target to source.
* **Circular reasoning** (error family 12). `satReducesToP_iff_inP_sat` shows that an argument whose key step is "SAT reduces to an easy problem" assumes its conclusion unless both the reduction and the decider are explicit.
* **Encoding-size mistakes** (error family 17). Machine languages are sets of bit strings, so the encoding is part of the language (for SAT, the shared `encodeCNF`). In the schema, the size functions `sa`, `sb` are explicit. Changing the encoding (for example unary numbers) changes what "polynomial" means.
* **Solving a different problem** (error family 5). A decider correct only on a promise does not compose. See Idea 32 for the formal counterexample and the promise version of this composition.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea29.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea29.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
