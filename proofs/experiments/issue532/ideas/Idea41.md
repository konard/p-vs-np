# Idea 41 — Williams' algorithmic method (fast circuit satisfiability ⇒ circuit lower bounds)

**Verdict:** Developed to an open obligation (conditional theorem proved). Williams' method turns a satisfiability algorithm into a circuit lower bound. The files state it in the shared machine model: if one machine decides satisfiability of NAND circuits with `n` inputs and `(n+1)^k` gates in `2^n / n^{ω(1)}` `Run` steps (`FastCircuitSAT`, the open obligation), then `NEXP ⊄ P/poly` (`williams_method`). Three known theorems enter as named explicit hypotheses: the nondeterministic time hierarchy (`NTimeHierarchy`), the easy-witness lemma (`EasyWitnessLemma`) and Williams' speedup construction (`WilliamsSpeedup`). The diagonal part of the hierarchy theorem is proved (`lazy_diagonal`, `nTimeHierarchy_of_lazyDiagonal`), leaving a pure simulation statement. The hierarchy hypothesis is the one [Idea 16](Idea16.md) states: both files use one class `NTIME(T)` (`inNTIME_iff_idea16`), Idea 16's `NTimeHierarchy` gives the one used here (`nTimeHierarchy_of_idea16`, `williams_method_idea16`), and the simulation statement for every `k ≥ 3` gives Idea 16's (`idea16_nTimeHierarchy_of_lazyDiagonal`). Idea 16's statement is itself a named known theorem, not a proof, so this replaces one hypothesis by a shared one; it does not remove it. The obligation is tied to P versus NP in both directions. `P = NP` implies it (`fastCircuitSAT_of_pEqualsNP`, proved from the membership of circuit satisfiability in NP, `CircuitSATInNP`, which is a named hypothesis here), so refuting it would prove `P ≠ NP` (`pNotEqualsNP_of_not_fastCircuitSAT`). Proving it gives `NEXP ⊄ P/poly`, which is not known to imply `P ≠ NP`. For `ACC⁰` circuits instead of general circuits the algorithm exists, and the method gives the unconditional `NEXP ⊄ ACC⁰` (Williams 2011) and `NQP ⊄ ACC⁰` (Murray–Williams 2018), which are cited and not mechanised.

## 1. The idea at full strength

Most lower-bound strategies look at a circuit class and try to show directly
that some explicit function is hard for it. Ideas 10, 16, 30 and 38 record
why the direct strategies stall: monotone bounds do not transfer,
diagonalization relativizes, and natural proofs are blocked by pseudorandom
functions.

Williams' algorithmic method runs the other way. It shows that an
**algorithm** for circuits yields a **lower bound** against them:

> If the satisfiability of circuits from a class `C` with `n` inputs and
> polynomially many gates can be decided in time `2^n / n^{ω(1)}`, only
> slightly faster than exhaustive search, then `NEXP ⊄ C`.

The proof is by contradiction. If `NEXP ⊆ C`, then every language of
`NTIME(2^n)` has short circuit witnesses (the easy-witness lemma). A
nondeterministic machine can guess such a witness circuit and check it with
the fast satisfiability algorithm. This decides every language of
`NTIME(2^n)` in nondeterministic time `2^n / n^{ω(1)}`, contradicting the
nondeterministic time hierarchy theorem.

The method has produced the strongest known lower bounds against
non-monotone circuit classes:

* `NEXP ⊄ ACC⁰` (Williams 2011), from an `ACC⁰`-satisfiability algorithm in
  time `2^{n - n^δ}`;
* `NQP ⊄ ACC⁰` (Murray–Williams 2018), from a stronger easy-witness lemma.

It combines a diagonalization (the hierarchy theorem) with a
circuit-specific algorithm that reads the gates of the circuit. The
algorithm does not relativize, because an oracle machine cannot inspect the
gates of an oracle circuit, and the argument does not produce a natural
property. So it passes the barrier audits of
[Idea 16](Idea16.md) (relativization), [Idea 30](Idea30.md) (natural proofs)
and [Idea 38](Idea38.md) (relativization audit). This is why it is added as a
separate direction.

## 2. Precise mathematical formulation

Everything is stated over the shared machine model
`proofs/complexity/lean/Complexity.lean` (`Machine`, `Run`, `pairedInput`)
and the shared circuit model `Issue532.Circuits` (NAND straight-line
programs, `WF`, `output`, `InPPoly`).

* **Nondeterministic time.** `AcceptsWithin m T x cert` means that the machine
  `m` started on `pairedInput x cert` accepts within `T` `Run` steps.
  `VerifiesIn m c T L` says two things. First, `m` halts within
  `c·T(|x|) + c` steps on every `pairedInput x cert` with
  `|cert| ≤ c·T(|x|) + c`. Second, for every `x`,
  `L x = true ↔ ∃ cert, |cert| ≤ c·T(|x|) + c ∧ AcceptsWithin m (c·T(|x|) + c) x cert`.
  `InNTIME T L :≡ ∃ m c, VerifiesIn m c T L`. The constant `c` absorbs
  constant factors and finitely many short inputs. The clock is the one of
  Idea 16's `InNTIME`, and `inNTIME_iff_idea16` proves that the two
  definitions agree.
* **NEXP and P/poly.** `expBound k n = 2^(n^k)`,
  `InNEXP L :≡ ∃ k, InNTIME (expBound k) L`, and
  `NEXPSubsetPPoly :≡ ∀ L, InNEXP L → InPPoly L`.
* **Circuit satisfiability.** `encCircuit n C` writes the number of inputs and
  the gate list with the unary prefix-free codes of `Machines.lean`.
  `CircuitSatisfiable n C :≡ ∃ x, |x| = n ∧ output x C = true`, and
  `CircuitSAT w = true` iff `w` encodes a well-formed satisfiable circuit.
  `CircuitSATInNP :≡ InNP CircuitSAT` is a known theorem, used only as a
  hypothesis.
  The [direct evaluator experiment](../../../../experiments/issue625/README.md)
  supplies an 83-state candidate with fourteen concrete runs checked in Lean
  and Rocq. Four paired universal phase proofs cover syntax rejection, entry
  into certificate matching, initial wire marking, and the final output pass.
  Its whole evaluator and polynomial runtime proofs remain open, so it does
  not discharge this hypothesis or satisfy the completion gate.
* **Exhaustive search.** `bruteCircuitSAT n C` evaluates `C` on the `2^n`
  vectors of `allAssignments n`. It evaluates `2^n · |C|` gates
  (`bruteForceGateEvaluations_eq`).
* **Open obligation.**
  `FastCircuitSAT :≡ ∀ k, ∃ m, ∀ c, ∃ n₀, ∀ n ≥ n₀, ∀ C, WF n C → |C| ≤ (n+1)^k →
  ∃ t b, t·(n+1)^c ≤ 2^n ∧ Run m (initial (encCircuit n C)) t b ∧ (b = true ↔ CircuitSatisfiable n C)`.
  The cost `t` is the `Run` step count of the machine `m`.
* **Known theorems, stated in the model and used only as hypotheses:**
  * `NTimeHierarchy :≡ ∃ c L, InNTIME (n ↦ 2^n) L ∧ ¬ InNTIME (n ↦ 2^n/(n+1)^c) L`.
    Idea 16 states the stronger `Idea16.NTimeHierarchy`, the same gap for
    every `k ≥ 3`, and `nTimeHierarchy_of_idea16` derives this one from it;
  * `SuccinctWitnesses`: for every verifier `VerifiesIn m c (expBound k) L`
    there is `d` such that every `x ∈ L` has an accepted certificate that
    is a prefix of `truthTable ℓ W` for a well-formed circuit `W` with at
    most `d·(|x|+1)^d` gates;
  * `EasyWitnessLemma :≡ NEXPSubsetPPoly → SuccinctWitnesses`;
  * `WilliamsSpeedup :≡ FastCircuitSAT → SuccinctWitnesses →
    ∀ c L, InNTIME (n ↦ 2^n) L → InNTIME (n ↦ 2^n/(n+1)^c) L`.
* **Lazy diagonalization.** `unary n` is the word `1^n`.
  `LazyDiagonalSimulation T T'` says that some `D ∈ NTIME(T)` follows every
  `L ∈ NTIME(T')` lazily: on some interval `l < u` it satisfies
  `D(1^n) = L(1^{n+1})` for `l ≤ n < u` and `D(1^u) = ¬L(1^l)`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `williams_method` | `NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup` and `FastCircuitSAT` imply `¬ NEXPSubsetPPoly`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `not_fastCircuitSAT_of_nexpSubsetPPoly` | Contrapositive: under the known theorems, `NEXP ⊆ P/poly` refutes the obligation. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `lazy_diagonal` | If `D` copies `L` one step ahead on `[l, u)` and flips `L(1^l)` at `1^u`, then `L ≠ D`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `nTimeHierarchy_of_lazyDiagonal` | `LazyDiagonalSimulation (2^n) (2^n/(n+1)^c)` implies `NTimeHierarchy`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `williams_method_lazy` | The method with the hierarchy theorem replaced by the simulation statement. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `inNTIME_iff_idea16` | Idea 41's `InNTIME` and Idea 16's `InNTIME` are the same class. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `nTimeHierarchy_of_idea16` | Idea 16's hierarchy statement implies the one used here. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `williams_method_idea16` | The method with Idea 16's hierarchy statement as the hypothesis. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `idea16_nTimeHierarchy_of_lazyDiagonal` | The simulation statement for every `k ≥ 3` implies Idea 16's hierarchy statement. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `fastCircuitSAT_of_inP` | A polynomial-time `CircuitSAT` decider meets the obligation. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `fastCircuitSAT_of_pEqualsNP` | `CircuitSATInNP` and `P = NP` imply `FastCircuitSAT`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `fastCircuitSAT_of_inP_sat` | `SATHard`, `CircuitSATInNP` and `InP SAT` imply `FastCircuitSAT`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `pNotEqualsNP_of_not_fastCircuitSAT` | Refuting the obligation proves `P ≠ NP`, given `CircuitSATInNP`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `pNotEqualsNP_of_nexpSubsetPPoly` | Under the known theorems, `NEXP ⊆ P/poly` would prove `P ≠ NP`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `not_nexpSubsetPPoly_of_pEqualsNP` | Under the known theorems, `P = NP` refutes `NEXP ⊆ P/poly`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `poly_le_two_pow` | For all `a, e` there is `N` with `a·(n+1)^e ≤ 2^n` for `n ≥ N`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `encCircuit_length_le` | A well-formed circuit with at most `(n+1)^k` gates has an encoding of length below `8·(n+1)^(2k+2)`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `encCircuit_injective` | The circuit encoding is injective. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `circuitSAT_encode` | `CircuitSAT (encCircuit n C) = true ↔ WF n C ∧ CircuitSatisfiable n C`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `bruteCircuitSAT_correct` | Exhaustive search over `allAssignments n` decides `CircuitSatisfiable n C`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `bruteForceGateEvaluations_eq` | Exhaustive search evaluates `2^n · |C|` gates. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `not_forall_inNTIME` | No time bound `T` puts every language in `NTIME(T)`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |
| `inNEXP_of_inNTIME_two_pow` | `NTIME(2^n) ⊆ NEXP`. | [Lean](../lean/Idea41.lean) | [Rocq](../rocq/Idea41.v) |

`FastCircuitSAT` is a `def … : Prop` in Lean and a `Definition … : Prop` in
Rocq. It is never assumed. `NTimeHierarchy`, `EasyWitnessLemma`,
`WilliamsSpeedup`, `LazyDiagonalSimulation` and `CircuitSATInNP` are true
statements of the literature. They are not mechanised here, and every use is
an explicit hypothesis. No theorem in either file proves or refutes P = NP.

The Rocq file uses no axioms (`Print Assumptions` reports "Closed under the
global context" for `williams_method`, `fastCircuitSAT_of_pEqualsNP`,
`pNotEqualsNP_of_not_fastCircuitSAT`, `lazy_diagonal`, `poly_le_two_pow`,
`not_forall_inNTIME`, and for the Idea 16 bridge `inNTIME_iff_idea16`,
`nTimeHierarchy_of_idea16`, `williams_method_idea16`,
`idea16_nTimeHierarchy_of_lazyDiagonal` and `inNEXP_of_inNTIME_two_pow`; the
last group is audited by `experiments/issue532_idea41/Assumptions.v`). It differs from Lean in these ways:

* **`CircuitSAT` is computable in Rocq.** Lean still defines the language by
  a classical `decide`, but now has the same exact decoder `decCircuit` and
  Boolean `wfFromb` check as Rocq. In both provers, `verifyCircuit` checks a
  bounded-length certificate and evaluates the shared NAND circuit.
  `circuitSAT_iff_verifyCircuit` proves that this executable check recognizes
  exactly the language. The decoder is a left inverse of `encCircuit` and
  rejects trailing bits. Rocq's `CircuitSAT` uses the decoder,
  well-formedness check, and `bruteCircuitSAT`; `circuitSAT_iff` shows it is
  exactly the Lean language. The `verifyCircuit` function is not yet a
  shared-model `Machine` with a proved polynomial `Run` bound.
* **`acceptedLanguage` is computable.** It enumerates the certificates of
  bounded length and replays each run with the step-bounded interpreter
  `runFor` (`acceptedLanguage_spec`).
* **`eq_acceptedLanguage` is pointwise.** Rocq has no function
  extensionality here, so the theorem is stated as
  `∀ x, L x = acceptedLanguage m c T x`.
* **`not_forall_inNTIME` inlines the Cantor diagonal.**
  `exists_language_not_in_family` concludes an inequality of functions, but
  a verifier determines its language only pointwise. So the file carries out
  the same diagonal directly, over the (machine, constant) encoding
  `encMachinePoly (m, c·(n+1)^0)` with a decoder built from `decMachinePoly`.
  The statement is the same as in Lean.
* **`lazy_chain` takes a pointwise premise** `∀ x, L x = D x`.
  `lazy_diagonal` keeps the Lean conclusion `L ≠ D`.

## 4. Complete argument

**The method.** Assume `NEXP ⊆ P/poly` and `FastCircuitSAT`. The
easy-witness lemma gives `SuccinctWitnesses`. With `FastCircuitSAT`,
Williams' speedup puts every language of `NTIME(2^n)` into
`NTIME(2^n/(n+1)^c)` for every `c`. The hierarchy theorem supplies a `c` and a
language of `NTIME(2^n)` outside `NTIME(2^n/(n+1)^c)`, a contradiction
(`williams_method`). The Lean proof is three lines, because the substance
sits in the three named hypotheses. The file states each of them over
`Complexity.Machine` with `Run` step counts, so none of them can be met by
choosing a cost function.

**What the speedup does** (Williams 2010, §3). Let `L ∈ NTIME(2^n)`. A
quasi-linear Cook–Levin reduction (Schnorr 1978; Robson 1991; Tourlakis
2001; Fortnow–Lipton–van Melkebeek–Viglas 2005) maps `x` to a Succinct-3SAT
instance: a circuit `F_x` of size `poly(n)` that, given a clause index `i`
of `n + O(log n)` bits, outputs the `i`-th clause of a 3-CNF `Φ_x` with
`2^n · poly(n)` clauses, such that `x ∈ L` iff `Φ_x` is satisfiable. The
verifier "guess an assignment of `Φ_x` and check it" is an NEXP verifier,
so under `NEXP ⊆ P/poly` it has succinct witnesses: a circuit `W` of size
`poly(n)` whose truth table satisfies `Φ_x`. The faster verifier guesses `W`
and builds the circuit `D(i)` = "clause `F_x(i)` is falsified by the values
`W` assigns to its three variables". `D` has `n + O(log n)` inputs and
`poly(n)` gates, and `x ∈ L` iff some `W` makes `D` unsatisfiable. The fast
algorithm decides this in time `2^{n + O(log n)} / n^{ω(1)} = 2^n / n^{ω(1)}`.

**Lazy diagonalization** (Žák 1983). Suppose that `D` copies `L` one step
ahead on `[l, u)` and flips `L(1^l)` at `1^u`, and that `L = D`. Then
`D(1^n) = L(1^{n+1}) = D(1^{n+1})` for `l ≤ n < u`, so
`D(1^l) = D(1^u)` by induction on the interval (`lazy_chain`). But
`D(1^u) = ¬L(1^l) = ¬D(1^l)`, a contradiction (`lazy_diagonal`). So a `D`
that follows every language of `NTIME(T')` lazily is not in `NTIME(T')`
itself (`not_inNTIME_of_lazyDiagonal`). If such a `D` is in `NTIME(2^n)`,
the hierarchy theorem follows (`nTimeHierarchy_of_lazyDiagonal`); one such
`D` for each `k ≥ 3` gives Idea 16's form of the theorem
(`idea16_nTimeHierarchy_of_lazyDiagonal`). The verifiers here are clocked:
they halt within the bound on every short certificate, as in
`Complexity.ClassNP` and Idea 16's `InNTIME`, which is what makes the two
classes equal. What is
not mechanised is the machine that realizes `D`. Inside the interval it
simulates the `i`-th verifier on `1^{n+1}` nondeterministically. At the end
of the interval it decides `L(1^l)` by exhaustive search, which fits in the
time budget because `u` is exponentially larger than `l`. The polynomial gap
`(n+1)^c` absorbs the logarithmic clock overhead of simulating on one tape.

**P = NP implies the obligation.** Under `P = NP` and `CircuitSATInNP`,
`CircuitSAT` has a machine `m` and a polynomial `p` with
`DecidesWithin m p CircuitSAT` (`polyDec_iff_inP`). Fix `k` and `c`. Every
gate of a well-formed circuit on `n` inputs reads a wire below `n + |C|`
(`wfFrom_bound`), so each gate code has at most `2(n + |C|)` bits, and
`|encCircuit n C| + 1 ≤ 8·(n+1)^(2k+2)` when `|C| ≤ (n+1)^k`
(`encCircuit_length_le`). The running time is therefore at most
`p.coefficient · 8^{p.degree} · (n+1)^{(2k+2)·p.degree}`. Multiplied by
`(n+1)^c`, this is below `2^n` from some `n` on (`poly_le_two_pow`). The proof
of `poly_le_two_pow` uses `n + 1 ≤ r·2^{⌊n/r⌋}` with `r = 2e + 2`, so
`(n+1)^e ≤ r^e · 2^{n/2}`, and `a·r^e ≤ 2^{n/2}` once `n ≥ 2a·r^e`.

**Non-vacuity.** `InNTIME T` is a family of languages indexed by a machine
and a constant. It has an injective encoding (`encMachinePoly`), so Cantor's
argument leaves a language outside it (`not_forall_inNTIME`). The obligation
is not satisfiable by choosing costs, since `t` is the step count of an
actual run of `m` on the encoded circuit. Nor is it refutable by a counting
argument: reading the input takes `poly(n)` steps, far below
`2^n / (n+1)^c`.

## 5. Known results and literature

* R. Williams, "Improving exhaustive search implies superpolynomial lower
  bounds", STOC 2010; SIAM J. Comput. 42(3), 2013. The method: a
  `2^n / n^{ω(1)}` circuit-satisfiability algorithm for poly-size circuits
  gives `NEXP ⊄ P/poly`.
* R. Williams, "Non-uniform ACC circuit lower bounds", CCC 2011; J. ACM 61(1),
  2014. An `ACC⁰`-satisfiability algorithm in time `2^{n - n^δ}` for circuits
  of size `2^{n^ε}` gives `NEXP ⊄ ACC⁰`.
* C. Murray and R. Williams, "Circuit lower bounds for nondeterministic
  quasi-polytime: an easy witness lemma for NP and NQP", STOC 2018. It gives
  `NQP ⊄ ACC⁰`.
* R. Impagliazzo, V. Kabanets and A. Wigderson, "In search of an easy
  witness: exponential time vs. probabilistic polynomial time", JCSS 65(4),
  2002. The easy-witness lemma: `NEXP ⊆ P/poly` implies that NEXP has
  succinct witnesses and that `NEXP = MA`.
* S. Cook, "A hierarchy for nondeterministic time complexity", JCSS 7(4),
  1973; J. Seiferas, M. Fischer and A. Meyer, "Separating nondeterministic
  time complexity classes", J. ACM 25(1), 1978; S. Žák, "A Turing machine
  time hierarchy", TCS 26(3), 1983. These are the nondeterministic time
  hierarchy theorems. Žák's proof is the lazy diagonalization of Section 4.
* C. P. Schnorr, "Satisfiability is quasilinear complete in NQL", J. ACM
  25(1), 1978; J. M. Robson, "An O(T log T) reduction from RAM computations
  to satisfiability", TCS 82(1), 1991. These are the quasi-linear Cook–Levin
  reductions behind the succinct instance `F_x`.
* S. Aaronson and A. Wigderson, "Algebrization: a new barrier in complexity
  theory", ACM TOCT 1(1), 2009. Proving `NEXP ⊄ P/poly` requires
  non-algebrizing techniques, so the general-circuit obligation is at least
  as hard as that.
* R. Williams, "Algorithms for circuits and circuits for algorithms", CCC
  2014. A survey of the method and its connections to the barriers.

## 6. How far the idea can be pushed toward P vs NP

* **Proved:**
  * the implication `FastCircuitSAT → ¬ NEXPSubsetPPoly` under three named
    known theorems (`williams_method`);
  * the diagonal core of the nondeterministic hierarchy theorem
    (`lazy_diagonal`, `nTimeHierarchy_of_lazyDiagonal`);
  * the identification of the hierarchy hypothesis with Idea 16's
    (`inNTIME_iff_idea16`, `nTimeHierarchy_of_idea16`,
    `williams_method_idea16`, `idea16_nTimeHierarchy_of_lazyDiagonal`);
  * `P = NP → FastCircuitSAT` from `CircuitSATInNP`
    (`fastCircuitSAT_of_pEqualsNP`), and hence
    `¬ FastCircuitSAT → P ≠ NP`;
  * the non-vacuity of the time classes.
* **Exact remaining obligation:** `FastCircuitSAT`, a machine that beats
  exhaustive search for general circuit satisfiability by a superpolynomial
  factor. It is open. Nothing known rules it out, and it is weaker than the
  Strong Exponential Time Hypothesis failing for circuits.
* **Two directions, two outcomes.**
  * Proving `FastCircuitSAT` gives `NEXP ⊄ P/poly`. That is a major open lower
    bound, but it is **not known to imply P ≠ NP**.
  * Refuting `FastCircuitSAT` proves `P ≠ NP`
    (`pNotEqualsNP_of_not_fastCircuitSAT`). A refutation is a lower bound
    against every machine, the same kind of statement as Idea 17's
    `AllAlgorithmsSuperpolynomial`.
* **Known theorems used as hypotheses:** `NTimeHierarchy` (or Idea 16's
  `Idea16.NTimeHierarchy`, or the simulation statement
  `LazyDiagonalSimulation`), `EasyWitnessLemma`, `WilliamsSpeedup`
  and `CircuitSATInNP`. The next slices are:
  1. the universal nondeterministic simulation behind
     `LazyDiagonalSimulation`;
  2. the finite-machine implementation and polynomial runtime proof for the
     now-specified circuit verifier behind `CircuitSATInNP`.
  The easy-witness lemma and the speedup construction are long proofs and
  are not attempted here.
* **For `P ≠ NP`** the method would need an NP-level version: a lower bound
  for `NP` itself, not for `NEXP` or `NQP`. Murray–Williams lowered the
  class from NEXP to NQP. No version reaching NP is known.

## 7. Failure modes this idea catches

* **Barrier audit** (Ideas 16, 30, 38; family 14 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): a proposed lower-bound technique
  should say which barrier it avoids and how. The method avoids
  relativization through the circuit-specific algorithm and natural proofs
  through diagonalization. A proof that uses only one of the two ingredients
  meets the barrier it failed to avoid.
* **Free cost functions** (family 11, and the review of PR #569): the obligation is a `Run`
  step count of a `Complexity.Machine`, so `t := 0` does not meet it. The
  checker enforces this for every open obligation.
* **Class confusion** (families 5 and 16): `NEXP ⊄ P/poly`
  and `NEXP ⊄ ACC⁰` are lower bounds for exponential-time classes. Neither
  is a statement about NP, and neither implies `P ≠ NP`.
* **Quantifier order** (Idea 34): `FastCircuitSAT` fixes the machine before
  the slack exponent `c` (`∀ k, ∃ m, ∀ c, ∃ n₀`). Swapping `∃ m` and `∀ c`
  gives a weaker statement that the speedup does not use.

## 8. Reproduction

Issue 625 adds a paired finite-machine **syntax** slice:
`Issue567.CircuitSyntax.circuitSyntaxMachine_run` (Lean) and
`CircuitSyntax.circuitSyntaxMachine_run` (Rocq) recognize precisely the
`encCircuit` grammar in `|x| + 1` steps, for every paired input. This is not
`CircuitSATInNP`: valid syntax can still contain forward wires, and certificate
length and gate evaluation remain to be implemented.
`circuitSATInNP_of_verifier_run` assembles the NP record from the full
machine's polynomial run theorem as an explicit hypothesis. It does not
discharge membership. The original `CircuitSATInNP` arguments are retained.
Both provers now run a mandatory CI completion gate that requires unconditional
membership, removal of those premises from the six issue 625 bridges, and
certification of the seven resulting targets. The required verification
summary fails while any of these obligations remains unresolved.
See [the remaining obligations](../../../../experiments/issue625/README.md).

From the repository root:

```sh
lake build proofs.experiments.issue532.lean.Idea41
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Machines.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Circuits.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea41.v
```

The commands print nothing beyond the build summary on success. Remove the
generated `.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
