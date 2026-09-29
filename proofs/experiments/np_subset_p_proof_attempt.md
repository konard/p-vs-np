# Routes to `NP ⊆ P`: an open experiment

This experiment revisits the proposed P = NP attempt from [PR #41](https://github.com/konard/p-vs-np/pull/41) (issue #8). The target is stated as **`NP ⊆ P`**, the shared `Complexity.PEqualsNP`. Its formal development is in [`issue8/`](issue8/README.md), with paired [Lean](issue8/lean/NPSubsetP.lean) and [Rocq](issue8/rocq/NPSubsetP.v) files. [`issue609/`](issue609/README.md) replaces PR #41's `PEqualsNPAttempt.lean` and `KnownBarriers.lean`. This document replaces PR #41's `experiments/p_equals_np_proof_attempt.md` and `experiments/p_equals_np_next_steps.md`. No theorem here settles P versus NP.

## The target and what it requires

`NP ⊆ P` says that every language with a polynomial-time verifier has a polynomial-time decider. `P ⊆ NP` is proved (`pSubsetNP`), so `NP ⊆ P` is the same as `P = NP`. Given the Cook–Levin hardness premise `SATHard`, it is equivalent to one statement: some `Complexity.Machine` decides the shared `SAT` language within a polynomial number of `Run` steps (`npSubsetP_iff_inP_sat`, `npSubsetP_iff_candidate`).

Issue #8 contributes a concrete solver for that statement. `dpllSAT` is a DPLL search proved equal to `SAT` on every word (`dpllSAT_eq_SAT`). It makes fewer than `2^(|w|+1)` recursive calls (`dpllSAT_calls_le`), and that bound is not polynomial (`calls_bound_not_polynomial`). A machine computing `dpllSAT` in polynomially many `Run` steps would prove `NP ⊆ P` with `SATHard` (`npSubsetP_of_dpll_machine`). Conversely, `NP ⊆ P` supplies such a machine (`dpll_machine_of_npSubsetP`), so this obligation is exactly as hard as the target.

## Checked boundary

| Claim | Current check |
| --- | --- |
| `NP ⊆ P ↔ PEqualsNP ↔ (P = NP as classes)` | Proved in paired Lean/Rocq files. |
| `NP ⊆ P ↔ SAT ∈ P` | Proved **conditionally** from `SATHard`. |
| DPLL decides the shared SAT language; the issue #610 formula is accepted and `[[]]` is rejected | Proved. |
| DPLL makes fewer than `2^(|w|+1)` calls | Proved. The bound counts calls, not `Run` steps. |
| A polynomial `Run` bound for any SAT machine | Not proved. It is equivalent to `NP ⊆ P` given `SATHard`. |
| `SATHard` (Cook–Levin hardness) in the shared model | Not discharged here. |
| `NP ⊆ P` or its negation | Not proved. |

## The routes, corrected

Each route below was proposed in PR #41's documents. For each one, the list states what the route actually gives.

1. **Exhaustive search and DPLL.** Exhaustive search takes `2^n` assignments. DPLL is correct once backtracking restores the state (issue #610; `dpll_correct`), but its worst case is exponential. DPLL without clause learning produces tree-like resolution refutations of unsatisfiable formulas. Resolution refutations of the pigeonhole formulas have exponential size (Haken 1985). The `O(1.308^n)` bound that PR #41 attributed to DPLL belongs to PPSZ, a **randomized** algorithm for **3-SAT** (Paturi–Pudlák–Saks–Zane 2005; Hertli 2011 proved the `1.30704^n` bound for general 3-SAT). It is not a DPLL bound and not a bound for general CNF-SAT.
2. **Reduction to 2-SAT.** 2-SAT is solvable in linear time (Aspvall–Plass–Tarjan 1979). Replacing `(x ∨ y ∨ z)` by its three 2-clauses is not equivalent, as PR #41 observed. PR #41 went further and concluded that no polynomial reduction exists. That is not known. A polynomial-time many-one reduction from SAT to 2-SAT exists **iff** `P = NP`, so ruling it out is as hard as `P ≠ NP`.
3. **Linear programming.** LP is in P (Khachiyan 1979). The natural SAT encoding needs 0/1 variables, which makes it integer programming, and 0-1 integer programming is NP-complete (Karp 1972). The LP relaxation admits fractional points. Extension-complexity lower bounds (Fiorini–Massar–Pokutta–Tiwary–de Wolf 2012; Rothvoss 2014) rule out polynomial-size LP formulations of the TSP and perfect-matching polytopes. These results concern specific polytopes; they do not refute every LP-based algorithm.
4. **Circuit upper bounds.** PR #41 treated polynomial-size circuits for SAT as a route to P = NP. `NP ⊆ P/poly` gives only the Karp–Lipton collapse `PH = Σ₂ᵖ` (Karp–Lipton 1980), not `P = NP`, because `P/poly` is non-uniform. Shannon's counting argument (1949) shows that most Boolean functions need circuits of size about `2^n/n`. It says nothing about SAT.
5. **Randomization.** Valiant–Vazirani (1986) is a **randomized** reduction from SAT to Unique-SAT. PR #41 claimed that Unique-SAT is NP-complete under deterministic reductions, which is not known. A polynomial-time algorithm for the Unique-SAT promise problem gives `NP = RP`. A bounded-error algorithm for SAT gives `NP ⊆ BPP` and then `NP = RP` (Ko 1982). Reaching `NP ⊆ P` from either would also need derandomization, for example `P = BPP` under the circuit hypothesis of Impagliazzo–Wigderson (1997).
6. **Algebraic encodings.** A CNF is satisfiable iff a **system** of polynomial equations has a 0/1 solution. The system has one equation `∏_{l ∈ c} (1 − val(l)) = 0` for each clause `c`, plus `x_i² = x_i`, where `val(x) = x` and `val(¬x) = 1 − x`. PR #41 used "the product of all clause polynomials = 0" instead, which holds as soon as **one** clause is satisfied. Degree lower bounds for Nullstellensatz and polynomial-calculus refutations exist for pigeonhole formulas (Razborov 1998) and random CNFs (Ben-Sasson–Impagliazzo 1999). They make degree-bounded Gröbner-basis methods exponential on those families.

## Corrections to PR #41's other claims

| PR #41's claim | Correction |
| --- | --- |
| Williams' ACC⁰ lower bound appeared at STOC 2011 | CCC 2011 (J. ACM 2014). The method gives circuit lower bounds, which is the `NP ⊈ P` direction ([issue #10](issue10/README.md)); it is not a route to `NP ⊆ P`. |
| The best general circuit lower bound is "~3.1n (Blum 1984, improved by Find & Yang 2022)" | Blum (1984) proved `3n − o(n)`. Find–Golovnev–Hirsch–Kulikov (FOCS 2016) proved `(3 + 1/86)n − o(n)`. Li–Yang (STOC 2022) proved `3.1n − o(n)`. |
| `NP ≠ coNP` is "believed easier" than `P ≠ NP` | `NP ≠ coNP` implies `P ≠ NP`, so it is the stronger statement. It holds iff no propositional proof system is polynomially bounded (Cook–Reckhow 1979). |
| Random 3-SAT is "usually unsatisfiable and hard" above the threshold | The hardest instances for DPLL are empirically near the threshold ratio `≈ 4.27` (Mitchell–Selman–Levesque 1992). Running time falls on both sides of it. Above it, resolution refutations are still exponential at constant density (Chvátal–Szemerédi 1988). |
| If P = NP, "average-case hardness might save crypto" | If P = NP, one-way functions do not exist: inverting a polynomial-time function is an NP search problem. This is Impagliazzo's "Algorithmica" (1995). Average-case hardness of NP cannot hold then either. |
| Independence "would need an oracle separating provability from truth" | This is not a meaningful condition. Independence from ZFC is a statement about provability; see [`proofs/p_vs_np_undecidable`](../p_vs_np_undecidable). Hartmanis–Hopcroft (1976) gave oracles relative to which `P^A = NP^A` is independent of set theory. That is a relativized result. |

## Historical sketches

The following material from PR #41 is historical. It is **not** in `main` and is not a proof.

* **`PEqualsNPAttempt.lean`.** It declared `axiom contradiction_from_separation : False`, from which `P_eq_NP_by_contradiction` followed. It also had axioms for a hypothetical solver, its time bound and its correctness, and it defined `SAT_Problem := fun _ => True`. `no_known_proof : RealPEqualsNPProof → False` asserted that no proof exists. `natural_proofs_barrier` and `algebrization_barrier` were axioms of type `True`. Two theorems were closed by `sorry`.
* **`KnownBarriers.lean`.** It stated the three barriers as axioms over placeholder classes such as `{ L // True }`. `ProofTechniqueRelativizes` reduced to `∀ A, True`, and three theorems were closed by `sorry`. Issue #609 replaced both files with axiom-free paired versions and proves the resulting counterexample (`false_technique_counterexample`).
* **The write-up's Lean sketch `p_equals_np_sketch`.** It closed the polynomial time bound and the correctness of a `hypothetical_solver` with `sorry`. Those two holes are exactly the open obligation stated above.
* **The next-steps plan.** It proposed files that were never created (for example `experiments/consequences_p_eq_np.md` and `proofs/experiments/CircuitComplexity.lean`), and a week-by-week schedule. It is superseded by the next ingredients in [`issue8/README.md`](issue8/README.md#next-ingredients-to-discharge).

## Next obligations

The next obligations are listed in [`issue8/README.md`](issue8/README.md#next-ingredients-to-discharge). The first is a `Complexity.Machine` for `dpllSAT` with an explicit exponential `Run` bound. The second is `SATHard` in the shared model. The third is a formal exponential lower bound for this `dpll`. None of them depends on the open problem, and none of them settles it.
