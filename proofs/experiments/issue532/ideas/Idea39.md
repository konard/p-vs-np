# Idea 39 — Proof-system scope (lower bounds and p-simulation)

**Verdict:** Correct tool, insufficient alone (general theorem proved)

In the Cook–Reckhow program, `NP ≠ coNP` (and hence `P ≠ NP`) would follow from
superpolynomial proof-size lower bounds for **every** propositional proof system.
The files prove the tools of that program in general form. Lower bounds transfer
downward along p-simulation with an explicitly composed polynomial, short proofs
transfer upward, and p-simulation is a preorder. They also prove that a lower
bound for one system, however strong, says nothing about systems that are not
p-simulated by it: a general countermodel has a weak system with a
superpolynomial lower bound and a strong system with linear-size proofs. This
refutes the inference "resolution lower bounds imply `NP ≠ coNP`".

## 1. The idea at full strength

A propositional proof system is a polynomial-time checkable relation "`π` proves
the tautology `φ`" that is sound and complete. Cook and Reckhow showed that
`NP = coNP` if and only if some proof system is *polynomially bounded*, meaning
every tautology `φ` has a proof of size polynomial in `|φ|`. The idea at full
strength:

1. prove superpolynomial lower bounds for stronger and stronger systems
   (resolution, cutting planes, bounded-depth Frege, Frege, extended Frege, ...);
2. conclude that no proof system is polynomially bounded, so `NP ≠ coNP`, and
   therefore `P ≠ NP`.

The typical invalid shortcut is to stop after step 1 for one system (usually
resolution, by Haken's theorem) and claim step 2. The honest version is a program
whose steps compose correctly only along p-simulations.

## 2. Precise mathematical formulation

- Polynomials are `Poly = ⟨c, k⟩` with `eval ⟨c, k⟩ n = c · (n+1)^k`, as in the
  repository's `proofs/complexity` library. The composed bound is
  `comp q p = ⟨q.c · (p.c + 1)^q.k, p.k · q.k⟩`.
- A system over formulas `F` is `System F = {Proof : Type; Proves : Proof → F →
  Prop; size : Proof → Nat}`. Polynomial-time checkability is not modelled; the
  theorems hold for every relation.
- `PSim S1 S2 q` means `S1` p-simulates `S2` with bound `q`: every `S2`-proof
  `π2` of `φ` converts to an `S1`-proof `π1` of `φ` with
  `size π1 ≤ q(size π2)`.
- `LowerBound S φs L`: every `S`-proof of `φs n` has size `≥ L n`.
- `PolyBounded S taut fsize p`: every tautology `φ` has an `S`-proof of size
  `≤ p(fsize φ)`.
- `SuperpolyLB S taut fsize`: for every `p` there is a tautology `φ` such that
  every `S`-proof of `φ` has size `> p(fsize φ)`.
- The open obligation is `SuperpolyAllSystems C taut fsize := ∀ S, C S →
  SuperpolyLB S taut fsize` for a class `C` of systems.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `tested` | a weak system with no proofs sits inside a strong one with a proof | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `poly_mono` | polynomial bounds are monotone | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `poly_comp_bound` | `q(p(n)) ≤ (comp q p)(n)` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `superpoly_not_bounded` | a superpolynomial lower bound rules out every polynomial bound | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `lower_bound_transfer_quant` | if `S1` simulates `S2` via `q` and `S1`-proofs of `φs n` need size `L n`, then `L n ≤ q(size π2)` for every `S2`-proof `π2` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `superpoly_transfer` | if `S1` p-simulates `S2`, a superpolynomial lower bound for `S1` gives one for `S2` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `poly_bounded_transfer` | if `S1` simulates `S2` via `q` and `S2` is bounded by `p`, then `S1` is bounded by `comp q p` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `psim_refl` | every system p-simulates itself | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `psim_trans` | `S1 ≥ S2` via `q` and `S2 ≥ S3` via `r` give `S1 ≥ S3` via `comp q r` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `exp_beats_poly` | `c · (n+1)^k < 2^n` for all `n ≥ 2^(2(c+k)+1)` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `sys_sound_complete` | the countermodel systems are sound and complete | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `weak_lb_strong_short` | general countermodel: `weak` has a superpolynomial lower bound, `strong` is polynomially bounded and p-simulates `weak` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `optimal_system_reduces` | if `S ∈ C` p-simulates all of `C`, the obligation for `C` is equivalent to a lower bound for `S` | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |
| `bounded_member_refutes` | one polynomially bounded member refutes the obligation | [Lean](../lean/Idea39.lean) | [Rocq](../rocq/Idea39.v) |

Helper lemmas `succ_le_two_pow`, `lt_two_pow_self`, `linear_lt_exp` and
`dyadic_bracket` are proved in both files. The definitions `Poly`, `System`,
`PSim`, `LowerBound`, `PolyBounded`, `SuperpolyLB`, `weakSys`, `strongSys` and
`SuperpolyAllSystems` appear in both files. Rocq uses `peval`/`pcomp` for Lean's
`Poly.eval`/`Poly.comp`. All proofs are constructive.

## 4. Complete argument

**Composition.** With `x = (n+1)^{p.k} ≥ 1`, we have
`p(n) + 1 = p.c · x + 1 ≤ (p.c + 1) · x`. Raising to the power `q.k` and
multiplying by `q.c` gives
`q(p(n)) = q.c · (p(n)+1)^{q.k} ≤ q.c · (p.c+1)^{q.k} · (n+1)^{p.k · q.k}`,
which is `(comp q p)(n)` (`poly_comp_bound`).

**Downward transfer.** Suppose `S1` p-simulates `S2` via `q` and `S1` has a
superpolynomial lower bound. Given a target polynomial `p`, apply the `S1` bound
to `comp q p`. This gives a tautology `φ` all of whose `S1`-proofs have size
`> (comp q p)(|φ|)`. If some `S2`-proof `π2` of `φ` had `size π2 ≤ p(|φ|)`, the
simulation would produce an `S1`-proof of size
`≤ q(size π2) ≤ q(p(|φ|)) ≤ (comp q p)(|φ|)`, a contradiction
(`superpoly_transfer`). The quantitative form `lower_bound_transfer_quant` keeps
explicit bounds `L n` instead.

**Upward transfer and preorder.** Composing the simulation with a polynomial
bound for `S2` gives one for `S1` (`poly_bounded_transfer`). Composing two
simulations gives `psim_trans`, and the identity gives `psim_refl`.

**Countermodel.** Let `taut` be any predicate on any type `F` with formulas of
unbounded size. Let both systems use `φ` itself as the proof of `φ` (so both are
sound and complete, `sys_sound_complete`). The weak system charges `2^{|φ|}`, the
strong one `|φ|`. Given `p = ⟨c, k⟩`, pick a tautology with
`|φ| ≥ 2^{2(c+k)+1}`. Then `p(|φ|) < 2^{|φ|}` by `exp_beats_poly`, so the weak
system has a superpolynomial lower bound. The strong system proves every `φ` in
size `|φ| ≤ |φ| + 1`, so it is polynomially bounded and has no superpolynomial
lower bound. It p-simulates the weak one because `|φ| ≤ 2^{|φ|} + 1`
(`weak_lb_strong_short`). Hence "`S` has a lower bound, and `S'` is stronger"
never implies "`S'` has a lower bound". Transfer goes only from the simulating
(stronger) system to the simulated (weaker) one.

**Reduction to one system.** If `C` contains a system `S` that p-simulates every
member (an *optimal* system), the obligation for `C` is equivalent to one lower
bound for `S` (`optimal_system_reduces`). Conversely, one polynomially bounded
member refutes the obligation (`bounded_member_refutes`).

## 5. Known results and literature

- S. A. Cook, R. A. Reckhow, "The relative efficiency of propositional proof
  systems", *Journal of Symbolic Logic* 44(1), 1979. They define proof systems
  and p-simulation, and prove that a polynomially bounded proof system exists if
  and only if `NP = coNP`. The abstract simulation calculus is formalized here.
  The equivalence with `NP = coNP`, which needs Turing machines and the
  coNP-completeness of TAUT, is **not** formalized.
- A. Haken, "The intractability of resolution", *Theoretical Computer Science*
  39, 1985. Resolution proofs of the pigeonhole principle `PHP^{n+1}_n` need
  exponential size. Not formalized (Idea 27 treats resolution itself).
- S. R. Buss, "Polynomial size proofs of the propositional pigeonhole
  principle", *Journal of Symbolic Logic* 52(4), 1987. Frege systems have
  polynomial-size proofs of the same formulas. This is a concrete instance of
  `weak_lb_strong_short`: resolution is weak and Frege is strong. Not
  formalized.
- J. Krajíček, P. Pudlák, "Propositional proof systems, the consistency of first
  order theories and the complexity of computations", *Journal of Symbolic
  Logic* 54(3), 1989. They study optimal proof systems; whether one exists is
  open. This is the hypothesis of `optimal_system_reduces`. Not formalized.
- No superpolynomial lower bound is known for Frege or extended Frege systems.
  The strongest systems with known superpolynomial lower bounds include
  bounded-depth Frege (Ajtai 1988, for the pigeonhole principle) and cutting
  planes. Not formalized.

## 6. How far the idea can be pushed toward P vs NP

**What is fully correct.** Along a chain `S_1 ≤ S_2 ≤ …` of p-simulations,
a lower bound for the top system gives lower bounds for everything below
(`superpoly_transfer`, `psim_trans`). The program therefore needs lower bounds
for ever stronger systems, and each new lower bound supersedes the old ones.

**Why it is insufficient alone.** The obligation `SuperpolyAllSystems` quantifies
over **all** Cook–Reckhow systems. By Cook–Reckhow it is equivalent to
`NP ≠ coNP`, which implies `P ≠ NP` but is not known to follow from it.
`optimal_system_reduces` shows the obligation would collapse to a single lower
bound if an optimal system existed, but that existence is itself open
(Krajíček–Pudlák). Without it, each lower bound covers only the systems it
p-simulates, and the countermodel shows nothing more can be concluded
formally.

**Current frontier.** Superpolynomial lower bounds are known for resolution,
cutting planes and bounded-depth Frege, but not for Frege. Frege lower bounds
are expected to face obstacles related to circuit lower bounds (Frege proofs
manipulate formulas, i.e. `NC^1` circuits), so the program meets the same
barriers as circuit complexity. The obligation is therefore at least as hard as
`NP ≠ coNP`, and in fact equivalent to it.

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 5 (solving an easier or different problem):** a lower bound for
  resolution (or another weak system) is a statement about that system only.
  `weak_lb_strong_short` shows it is consistent with short proofs elsewhere.
- **Family 20 (structure theorem from one algorithm class):** "SAT solvers based
  on resolution need exponential time" does not cover all algorithms, nor all
  proof systems.
- **Family 14 (barriers):** lower bounds for Frege-like systems are tied to
  circuit lower bounds and face the same barriers.
- **Family 12 (circular reasoning):** assuming an optimal proof system exists
  and then deriving `NP ≠ coNP` from one lower bound uses an open hypothesis;
  `optimal_system_reduces` makes that hypothesis explicit.

Audit rule: for a claim "lower bound for `S` implies `NP ≠ coNP`", ask for a
proof that `S` p-simulates every proof system. Without it, the claim is a
lower bound for `S` only.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea39.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea39.v
rm -f proofs/experiments/issue532/rocq/Idea39.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea39.aux
```

Both commands print nothing on success.
