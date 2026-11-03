# Fidelity audit: do the labs' Lean statements say "ETH is false"?

A kernel check proves *a* statement. This audit asks whether that statement
means what the papers claim. It reads the two trusted statement files
line by line and compares them with the textbook hypothesis and with this
repository's definition.

* Anthropic: [`sources/anthropic-formal-math-eth/MainResults.lean`](sources/anthropic-formal-math-eth/MainResults.lean)
  (`anthropics/formal-math@16a5ce4`, Lean v4.33.1).
* OpenAI: [`sources/openai-math/lean/ComparatorChallenges/SubexponentialSAT.lean`](sources/openai-math/lean/ComparatorChallenges/SubexponentialSAT.lean)
  and its Comparator config [`SubexponentialSAT.json`](sources/openai-math/lean/ComparatorChallenges/SubexponentialSAT.json)
  (`openai/math@4eaee87`, Lean v4.34.1).
* This repository: [`proofs/experiments/issue638/lean/ETH.lean`](../../../proofs/experiments/issue638/lean/ETH.lean)
  and [`rocq/ETH.v`](../../../proofs/experiments/issue638/rocq/ETH.v).

The CI workflow checks that the trusted files it builds are byte-identical to
the copies in `sources/`. So this audit is about the same text that the
kernels check.

## 1. Reference: the textbook ETH

Impagliazzo and Paturi (*On the complexity of k-SAT*, JCSS 62, 2001) define
`s_k = inf { δ : k-SAT is decidable in time O(2^{δn}) }` and
**ETH: `s_3 > 0`**. The running time is measured in `n`, the number of
variables. A factor polynomial in the input length is customarily allowed
(`O*`). This is harmless for fixed `k`, because a k-CNF without repeated
clauses has `O(n^k)` clauses. ETH is false iff for every `δ > 0`, 3-SAT can be
decided in time `O*(2^{δn})`.

## 2. Anthropic (`MainResults.lean`)

| Item | Lean text | Matches textbook? | Remark |
|---|---|---|---|
| Machine | `Turing.TM2ComputableAux Bool Bool` with `∀ i, Finite (M.tm.Γ i)` | yes | Mathlib's multi-stack machine. Finite program, finite states, and *all* stack alphabets finite (the extra hypothesis closes a Mathlib loophole in which only the input alphabet must be finite). A stack machine with finitely many stacks simulates and is simulated by a multi-tape TM with polynomial overhead. |
| Time | `TM2OutputsInTime … (t n)`; one step runs one labelled block | yes | For a fixed machine a block is a bounded number of stack operations, so steps and elementary operations differ by a constant. |
| Formula | `List (List (Fin n × Bool))`, `IsKCNF k φ := (∀ C ∈ φ, C.length ≤ k) ∧ φ.Nodup` | yes, slightly restricted | No repeated clause; literals in a clause may repeat. The file explains why: without a bound on `m`, no bound in `n` alone is possible, because the machine must read the input. The textbook bound `m = O(n^k)` follows. |
| Encoding | `encClauses`: `1ⁿ0`, then `k` slots of `⌊log₂ 2n⌋+1` bits per clause | yes | A standard binary encoding. The rewrite from any reasonable encoding is polynomial in `n` and is argued in the header comment, not in Lean. |
| Correctness | `DecidesKSat`: output bit `b` with `b = true ↔ Satisfiable φ` | yes | `Satisfiable` is the standard definition. |
| Time bound | `InTime k δ`: one machine and one `c : ℕ` with `t n = ⌊c · 2^{δn}⌋` | **stronger** than textbook | No polynomial factor at all. The machine and `c` may depend on `k` and `δ`, as in the textbook. |
| `s_k` | `⨅ δ : ℝ≥0, ⨅ (_ : InTime k δ), (δ : ℝ≥0∞)` | yes | Valued in `[0, ∞]`. If no `δ` works, `s_k = ⊤ > 0`, so ETH is *not* vacuously false. |
| ETH | `0 < s 3` | yes | Deterministic algorithms. Refuting the deterministic form also refutes the randomized form (comment in the file). |
| Claim | `ETHIsFalse := ¬ ETH` | yes | Equivalent to `∀ δ > 0, InTime 3 δ` because `InTime` is monotone in `δ`. |
| Main Theorem | one `M`, one `C : ℕ` for **all** `k ≥ 1`, `n ≥ 4`, `m ≥ 2`, `IsKCNF`, `AllOccur`; output `binary n (numSat φ)` within `⌊2^{C·min(km/√lg m, k²n·lg lg n/√lg n)}⌋` | stronger than needed for ETH | Counts models (#SAT), uniform in `k`. The side conditions `n ≥ 4`, `m ≥ 2`, `AllOccur` only exclude inputs where the formula for the bound is undefined or trivial, as the docstring explains. |

**Findings (Anthropic).**

1. `ETHIsFalse` is a faithful, slightly *stronger* formalization of "ETH is
   false". It gives a time bound with no polynomial factor and requires only
   that no clause is repeated.
2. The bridge from `TM2` to "an algorithm in the usual sense" (RAM simulation,
   input rewriting) is argued in prose, not in Lean. It is a standard
   polynomial-overhead simulation and does not affect `s_3 = 0`. However, it is
   exactly the gap that blocks planned issue **P8** in this repository.
3. The constants are not explicit. The Main Theorem's exponent
   `k²n·lg lg n/√lg n` drops below `δn` only when `√lg n > k²·C·lg lg n/δ`. With
   any realistic `C`, this happens only for astronomically large `n`. The
   result is asymptotic and has no practical consequence for SAT solving.
4. Upstream CI runs Comparator with the independent `nanoda` kernel
   (`enable_nanoda: true`). Our workflow repeats that check at the same pin.

## 3. OpenAI (`SubexponentialSAT.lean`)

| Item | Lean text | Matches textbook? | Remark |
|---|---|---|---|
| Machine | `PrimitiveMachine`: `tapeCount`, `stateCount : ℕ`; each state scans one tape; a transition halts with a `Bool` or does one `Turing.TM0.Stmt (Option Bool)` (move or write) | yes | A deterministic multi-tape TM with finitely many states, alphabet `{none, some false, some true}`, one head action per step. This model is closer to the textbook TM than Anthropic's. |
| Formula | `CNF V := Finset (Clause V)`, `Clause V := Finset (Literal V)`, `WidthAtMost k F := ∀ C ∈ F, C.card ≤ k` | yes | Sets of sets: no repeated clause or literal. |
| Encoding | `encodeCNF F = encodeNat n ++ encodeList (encodeList encodeNat) (sorted literal codes)` | yes | Canonical (sorted) and self-delimiting (`frame`). Variable count and literal codes are written in **unary**. So `L = formulaBitLength F = O(m·k·n)`. That is still polynomial in `n` for fixed `k`, but it is larger than a binary encoding. |
| Quantifiers | `∀ k ≥ 2, ∃ machine C A S d e, ∀ n F, WidthAtMost k F → …` | yes | One machine **per `k`**, as in the textbook. Not uniform in `k`, unlike Anthropic's Main Theorem. |
| Correctness | `final.state = Sum.inl (decide (0 < count F))`, and the count tape holds `countWord (count F)` | yes | Decides SAT in the halting state and writes the model count in binary. The count is `card` of the satisfying assignments in `Fin n → Bool`. |
| Time bound | `time ≤ C·(L+1)^d · 2^{A·runtimeScale n}` with `runtimeScale n = n·(log log (n+16))²/√log (n+16)` (natural log) | yes (`O*` form) | The polynomial factor `(L+1)^d` is the usual `O*`. Since `L = poly(n)` for fixed `k`, it is `2^{O(log n)}`. The `+16` shift and the base `e` change only constants. The exponent is `o(n)`, so the bound is below `C_δ·2^{δn}` for every `δ > 0`. |
| Space | at every prefix of the run, visited cells `≤ S·(L+1)^e` | extra | Polynomial space. This is not needed for ETH, but it is part of the theorem. |
| ETH itself | **not stated** | — | The challenge states the algorithm. The step "this algorithm ⇒ `s_3 = 0`" is a short informal argument outside Lean. |
| Exponent vs paper | Lean: `(log log n)²`; paper: `log log n` | weaker than the paper | [`docs/378.md`](sources/openai-math/lean/docs/378.md) says so explicitly. Both bounds refute ETH. |
| Comparator | `permitted_axioms: propext, Quot.sound, Classical.choice`; `enable_nanoda: false` | — | Upstream does not use the second kernel. Our `openai-full` job forces `enable_nanoda=true`, and nanoda accepts (run [41591216557](https://github.com/konard/p-vs-np/actions/runs/41591216557)). |
| `E^NP` lower bound | **not formalized** | — | Recorded as planned issue P12. |

**Findings (OpenAI).**

1. `exact_count_and_sat` is a faithful formalization of "for each `k ≥ 2`,
   #k-SAT (hence k-SAT) is decidable in time `O*(2^{o(n)})`". For `k = 3` this
   implies `s_3 = 0`, which is the negation of ETH. The final deduction is not
   in Lean, but it is elementary: `runtimeScale n = o(n)` and `L = poly(n)`.
2. The formal exponent is weaker than the paper's. This is not an error. It
   does mean that the sharper claims (`n·log log n/√log n`, and `n/√log n` for
   linear clause density) are informal only.
3. The `E^NP` superlinear circuit lower bound in the same paper is not
   covered by any Lean statement.

## 4. Relation to this repository's definitions

Our `ETH` (`ETH.lean`, `ETH.v`) is `∃ d > 0, ¬ KSATExpTime 3 1 d`, where
`KSATExpTime k a d` allows the factor `(|x|+1)^c` and uses `2^{⌊a·n/d⌋}`. So
it is the textbook `O*` form with `δ = 1/d`.

| Lab statement | Implies our `SubexpKSAT 3` (hence `¬ ETH` by `eth_iff_not_subexp3`)? | Missing piece |
|---|---|---|
| Anthropic `ETHIsFalse` | yes, once `InTime 3 δ` is moved to `Complexity.Machine`: a bound without a polynomial factor is a special case of `expTime` | TM2 → `Complexity.Machine` simulation; `encClauses` → our `encodeCNF` translation (**P8, blocked**) |
| OpenAI `exact_count_and_sat 3` | yes, once moved: `(L+1)^d` fits `(|x|+1)^c` up to the encoding blow-up, and `2^{A·runtimeScale n} ≤ C_δ·2^{δn}` (the same argument as `logBudget_gap`) | `PrimitiveMachine` → `Complexity.Machine` simulation; encoding translation; the real-analysis bound `runtimeScale n = o(n)` (**P8, blocked**) |

Both lab theorems are therefore **consistent** with this repository's
definitions. Neither is imported, so in this repository `SubexpKSAT 3`
remains a named hypothesis.

## 5. What no statement says

* Neither statement mentions `P` or `NP`. `logBudget_gap` (proved here)
  shows that subexponential bounds of this kind are superpolynomial in
  general. In particular, `2^{n·polyloglog n/√log n}` is not polynomial, so
  `P = NP` does not follow.
* Neither says anything about SETH directly. OpenAI's theorem covers every
  `k ≥ 2` with an `o(n)` exponent, and Anthropic's covers every `k ≥ 1`. Each
  therefore gives `SubexpAllK`, hence `¬ SETH` by `not_seth_of_subexpAllK`,
  under the same transfer as above.
* Neither covers randomized lower bounds, circuit size, or quantum
  algorithms.

## 6. Verdict

| Question | Anthropic | OpenAI |
|---|---|---|
| Faithful to "ETH is false"? | **yes** (stated directly, slightly stronger) | **yes** (the algorithm is stated; ETH follows by an elementary informal step) |
| Vacuity risks found? | none (`s_3 = ⊤` when no `δ` works; all alphabets finite; output through bijections with `Bool`) | none (finite states, three-symbol alphabet, explicit `Trace`) |
| Gaps between Lean and paper | TM2 → RAM bridge is prose | sharper exponent and `E^NP` lower bound are prose |
| Second kernel | nanoda upstream and in our CI | not upstream; forced in our `openai-full` job, where nanoda accepts |

This audit was done by reading the statements. It is not a formal proof of
fidelity. The formal part is the transfer in P8, which is blocked.
