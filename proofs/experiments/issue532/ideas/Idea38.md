# Idea 38 — Relativization audit (oracle query lower bound)

**Verdict:** Refuted in full strength (published theorem) + formal core

The idea is to settle P vs NP with techniques that treat machines as black boxes
with access to an oracle: simulation, diagonalization, and query counting. Baker,
Gill and Solovay (1975) refuted this route in full strength. They gave an oracle
`A` with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`, so no argument that
relativizes can settle the question. The files machine-check the combinatorial
core of the oracle `B` for every tree and every `N`: a decision tree of depth
`< N` cannot decide whether an `N`-bit oracle segment contains a `true`, while one
nondeterministic query suffices. They also prove the abstract meta-theorem that a
relativizing proof method settles no statement that holds for one oracle and fails
for another. In the shared machine model (with the oracle machines of Idea 16) the
NP side is proved outright: an explicit one-query oracle machine puts the BGS test
language in `NP^A` for every oracle `A` (`testLangO_inNPO`), and under the named
BGS hypotheses no relativizing method proves `P^A = NP^A` or its negation for all
oracles (`machineRelativizing_cannot_settle`).

## 1. The idea at full strength

Many attempted proofs of `P ≠ NP` (and of `P = NP`) use only the following
properties of machines:

- a machine can simulate another machine with small overhead;
- machines can be enumerated and diagonalized against;
- a computation can be run step by step, and each step inspects a few bits.

Each of these properties survives when every machine gets the same oracle `O`
(an extra tape answering "is `x ∈ O`?" in one step). An argument using only them
therefore proves a statement about `P^O` vs `NP^O` for **every** oracle `O`
simultaneously. At full strength the idea is: *find such a black-box argument
that separates (or collapses) P and NP.*

The honest version of the idea is an audit tool. Given a claimed proof, ask
whether every step remains true when all machines receive an oracle. If so, the
proof relativizes and cannot be correct, because of the two BGS oracles.

## 2. Precise mathematical formulation

- An oracle is `O : Nat → Bool`.
- A deterministic oracle computation on a fixed input is modelled as an adaptive
  decision tree:

      inductive Tree | leaf (b : Bool) | query (i : Nat) (t0 t1 : Tree)

  `eval O (query i t0 t1)` continues in `t1` if `O i = true` and in `t0`
  otherwise. `depth` is the maximal number of queries along a path, and it is a
  lower bound on running time. A deterministic oracle machine running in time
  `c · (n+1)^k` on input `1^n` unfolds into such a tree of depth at most
  `c · (n+1)^k`, since the input is fixed and only oracle answers branch.
- `allFalse` is the empty oracle; `single j` is the oracle true exactly at `j`.
- The BGS test language is `L_O = {1^n : ∃ j < 2^n, O j = true}`, where
  positions `j < 2^n` encode the strings of length `n`. It is in `NP^O`: guess
  `j` and make one query.
- Abstractly, a proof method is a predicate `Proves` on oracle-indexed
  statements `S : (Nat → Bool) → Prop`. It is `Relativizing` if
  `Proves S → ∀ O, S O`.
- The generic schema is `NonrelativizingIngredientFor Proves := ∃ S O, Proves S ∧ ¬ S O`.
  It quantifies over a free method `Proves`, so it is a schema, not an open
  obligation.
- **Machine part (shared model, oracle machines of Idea 16).** An oracle is a
  language `A : Oracle`. `testVerifier` is an explicit oracle machine that reads
  `pairedInput x cert` and makes one query on `x ++ true :: cert`.
  `testLangO A x :≡ ∃ y, |y| ≤ |x| + 1 ∧ A (x ++ true :: y)` is the BGS test
  language. The known theorem (Baker–Gill–Solovay 1975) is the named hypothesis
  `BGSTestSeparation := ∃ B, ¬ InPO B (testLangO B)`, together with Idea 16's
  `BGSCollapse := ∃ A, PEqualsNPO A`. A method is
  `MachineRelativizing Proves := ∀ S, Proves S → ∀ A, S A`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `tested` | small illustration kept from an earlier round (not a main result): some predicate on `Bool` holds at `false` and fails at `true` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `falsePath_length` | the all-false path queries at most `depth T` positions | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `eval_single_of_not_mem` | if `j` is not queried on the all-false path, `T` answers the same on `single j` and `allFalse` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `exists_not_mem` | a list of length `< N` misses some `j < N` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `shallow_tree_misses` | `depth T < N` gives `j < N` with `eval allFalse T = eval (single j) T` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `no_shallow_tree_decides_or` | no tree of depth `< N` decides `∃ j < N, O j = true` for all `O` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `orTree_depth` | the sequential tree `orTree N` has depth exactly `N` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `orTree_correct` | `orTree N` decides `∃ j < N, O j = true` for every `O` (the bound is tight) | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `verifier_one_query` | with a guessed `j`, a depth-1 tree verifies the same property | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `exp_beats_poly` | `c · (n+1)^k < 2^n` for all `n ≥ 2^(2(c+k)+1)` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `bgs_core` | every tree family of depth `≤ c · (n+1)^k` fails on `2^n` positions for some `n` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `relativizing_cannot_prove` | a relativizing method cannot prove a statement false for some oracle | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `relativizing_cannot_decide` | if `S A` and `¬ S B`, a relativizing method proves neither `S` nor `¬ S` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `nonrelativizing_needed` | a method that settles such an `S` has a nonrelativizing ingredient | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `NonrelativizingIngredientFor` (def) | schema: the method proves some statement that fails for some oracle; never assumed | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `nonrelativizing_iff` | `NonrelativizingIngredientFor Proves ↔ ¬ Relativizing Proves` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `testVerifier_run` | the oracle machine `testVerifier` halts on `pairedInput x cert` in `2·|x| + 4` steps with answer `A (x ++ true :: cert)` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `testLangO_inNPO` | for every oracle `A`, `InNPO A (testLangO A)` (NP side of BGS, in the machine model) | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `BGSTestSeparation` (def) | known theorem, not mechanised here: some oracle `B` has `testLangO B ∉ P^B` | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `bgsSeparation_of_testSeparation` | `BGSTestSeparation → BGSSeparation` (Idea 16's `∃ B, ¬ PEqualsNPO B`) | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `MachineRelativizing` (def) | a method over oracle-indexed machine statements relativizes | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |
| `machineRelativizing_cannot_settle` | under `BGSCollapse` and `BGSTestSeparation`, a relativizing method proves neither `PEqualsNPO` nor its negation for all oracles | [Lean](../lean/Idea38.lean) | [Rocq](../rocq/Idea38.v) |

Helper lemmas `succ_le_two_pow`, `lt_two_pow_self`, `linear_lt_exp` and
`dyadic_bracket` are proved in both files. Everything is constructive except
`nonrelativizing_iff`, whose backward direction uses excluded middle
(`Classical.byContradiction` in Lean, `NNPP` from `Classical_Prop` in Rocq).
Neither file declares axioms. Both files check `orTree 2` on `single 1` by
computation. The Lean file imports Idea 16 for the oracle machines. The intended
Rocq names are the Lean names; the Rocq file still has the pre-machine version
(old name `NonrelativizingIngredient`, no machine part).

**Label.** The issue's list names Idea 38 as a natural-proofs idea, but this file
and dossier are the relativization audit (BGS). Natural proofs are treated in
Idea 10.

## 4. Complete argument

**Step 1 (the invisible position).** Follow `T` on the all-false oracle and
record the queried positions in `falsePath T`. This list has length at most
`depth T` (`falsePath_length`), by induction on `T` using
`length (falsePath t0) ≤ depth t0 ≤ max (depth t0) (depth t1)`.

**Step 2 (counting).** A list `L` with `length L < N` misses some `j < N`
(`exists_not_mem`). The proof is by induction on `N`. If `N ∉ L`, take `j = N`
(for the successor). Otherwise remove `N` from `L`, which shortens it, apply the
induction hypothesis, and note that the `j < N` found is not `N`, so it was not
in `L` either.

**Step 3 (indistinguishability).** If `j ∉ falsePath T`, then on the oracle
`single j` every query along the all-false path is answered `false` (the queried
`i` differs from `j`). The computation therefore follows the same path and
returns the same leaf (`eval_single_of_not_mem`, induction on `T`). With Step 2
this gives `shallow_tree_misses`.

**Step 4 (lower bound).** Suppose `T` decided `∃ j < N, O j = true` for all `O`.
On `single j` the answer must be `true`, and on `allFalse` it must be `false`.
Step 3 says the two answers are equal, which is a contradiction
(`no_shallow_tree_decides_or`).

**Step 5 (tightness and nondeterminism).** `orTree N` queries `N-1, …, 0` in turn
and has depth exactly `N` (`orTree_depth`, `orTree_correct`). So the lower bound
`N` is exact for deterministic trees. A nondeterministic machine guesses `j` and
queries once (`verifier_one_query`).

**Step 6 (polynomial against exponential).** Take `N = 2^n`. If the trees
`trees n` have depth `≤ c · (n+1)^k`, then at `n = 2^(2(c+k)+1)` the depth is
`< 2^n` (`exp_beats_poly`). Step 4 then gives `bgs_core`. This is the heart of
BGS: for each polynomial-time deterministic oracle machine `M_i` there is a
length `n_i` and a position the machine never looks at.

**What BGS add (not formalized).** Baker–Gill–Solovay build one oracle `B` by
stages that defeat every machine `M_i` in turn. At stage `i` they pick a fresh
length `n_i`, run `M_i` on `1^{n_i}` with the oracle built so far, and, if `M_i`
rejects, put an unqueried string of length `n_i` into `B`. Step 4 guarantees that
such a string exists. Then `L_B ∈ NP^B \ P^B`. For the collapse they take `A` to
be a PSPACE-complete language, giving `P^A = PSPACE = NP^A`.

**Step 7 (meta-theorem).** Let `S O` be the statement "`P^O = NP^O`". BGS give
`S A` and `¬ S B`. A relativizing method proves only statements true for all
oracles, so it proves neither `S` nor `¬ S` (`relativizing_cannot_decide`). Any
successful method must prove some statement that fails for some oracle
(`nonrelativizing_needed`), which is the definition of a nonrelativizing
ingredient.

**Step 8 (machine model).** `testVerifier` moves right across `x`, checks the
separator, returns to the start and queries the bits `x ++ true :: cert`; this
takes `2·|x| + 4` steps (`testVerifier_run`). With certificate bound `|x| + 1`
this puts `testLangO A` in `NP^A` for every `A` (`testLangO_inNPO`). So an
oracle `B` with `testLangO B ∉ P^B` (the named BGS hypothesis
`BGSTestSeparation`) gives `¬ PEqualsNPO B` (`bgsSeparation_of_testSeparation`).
With `BGSCollapse`, a relativizing method proves neither `PEqualsNPO` nor its
negation for all oracles (`machineRelativizing_cannot_settle`). By Idea 16
(`pEqualsNP_of_all_oracles`, `pNotEqualsNP_of_all_oracles`), those are the only
routes by which an all-oracle statement reaches the real classes.

## 5. Known results and literature

- T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP question",
  *SIAM Journal on Computing* 4(4), 1975. They construct oracles `A`, `B` with
  `P^A = NP^A` and `P^B ≠ NP^B`. The query lower bound (Steps 1–6) is formalized
  here. The stage-by-stage construction of `B` against an enumeration of oracle
  machines, and the oracle `A` via a PSPACE-complete set, are **not** formalized.
  Nor is the translation from oracle Turing machines to decision trees.
- A. Shamir, "IP = PSPACE", *Journal of the ACM* 39(4), 1992 (building on Lund,
  Fortnow, Karloff and Nisan, same issue). This is a nonrelativizing result:
  there are oracles relative to which `IP ≠ PSPACE`. Its key ingredient is
  arithmetization, which extends Boolean formulas to low-degree polynomials over
  a finite field. Not formalized.
- S. Aaronson, A. Wigderson, "Algebrization: A New Barrier in Complexity
  Theory", *ACM Transactions on Computation Theory* 1(1), 2009. They show that
  arithmetization-based techniques "algebrize", and that algebrizing techniques
  also cannot resolve P vs NP. Not formalized.
- The companion barriers are natural proofs (A. Razborov, S. Rudich, "Natural
  proofs", *JCSS* 55(1), 1997) and algebrization. A resolution must avoid all
  three. Idea 2 in this directory treats the unrelativized black-box search
  bound, and Idea 10 discusses natural proofs for circuit lower bounds.

## 6. How far the idea can be pushed toward P vs NP

**At full strength the route is refuted.** A proof that uses only relativizing
steps would prove the same statement for the oracles `A` and `B`. One of those
instances is false, so no such proof exists. The formal `bgs_core` shows the
combinatorial reason why query-based ("black-box") reasoning cannot beat
nondeterminism relative to `B`: at a suitable length `n`, polynomially many
queries miss almost all of the `2^n` positions. The oracle `B` itself is cited
from BGS, not formalized.

**What remains is a precise requirement, not an open obligation.** The schema
`NonrelativizingIngredientFor Proves` asks for a method that proves a statement false relative to some oracle. By
`nonrelativizing_iff` it is equivalent to the method not being relativizing.
Known nonrelativizing techniques include:

- arithmetization (IP = PSPACE, MIP = NEXP);
- the local checkability behind the PCP theorem (whether the PCP theorem
  itself relativizes depends on how oracle access to the proof is modelled);
- circuit lower bounds that inspect the structure of computation (for example
  Williams' 2011 ACC lower bound combines a nontrivial ACC-SAT algorithm with
  diagonalization, and uses the circuit structure, not only oracle access).

Arithmetization, however, algebrizes, and Aaronson–Wigderson show that
algebrizing techniques also cannot resolve P vs NP. So the requirement is
necessary but far from sufficient. It must be met by a technique that also
escapes algebrization and natural proofs. No such technique is known.

**Why it is at least as hard as the original problem.** Any proof of `P ≠ NP` or
`P = NP` is itself a method meeting the requirement for `S O = (P^O = NP^O)`,
by Step 7 together with the BGS oracles (named hypotheses, not formalized). The
requirement is therefore a necessary condition that every
resolution satisfies, not a shortcut.

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 14 (ignoring known barriers):** any claimed proof whose steps are
  simulation, enumeration and diagonalization, or "the machine must look at
  every candidate", relativizes. `relativizing_cannot_decide` shows it cannot
  be correct.
- **Family 13 (diagonalization misuse):** diagonalization by itself relativizes
  (the time hierarchy theorem holds relative to every oracle). It cannot
  separate P from NP without a nonrelativizing ingredient.
- **Family 15 (verification vs search):** `verifier_one_query` versus
  `no_shallow_tree_decides_or` is the exact query-model gap between verifying
  and searching. It holds only in the oracle world. Transferring it to
  unrelativized P vs NP is the classic invalid step.
- **Family 1 (lower bound assumed):** "an algorithm must examine all `2^n`
  assignments" is true for black-box oracle access (this file) and unproven for
  algorithms that read the formula.

Audit rule: for each step of a proof, check whether it stays valid when every
machine gets the same oracle. If all steps do, the proof is wrong.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea38.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea38.v
rm -f proofs/experiments/issue532/rocq/Idea38.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea38.aux
```

Both commands print nothing on success.
