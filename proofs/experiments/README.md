# P vs NP Proof Experiments

This directory contains experiments toward, and audits of, P vs NP arguments. No resolution of P vs NP is claimed. The formal target and its status are described in [FORMAL_STATEMENT.md](../../FORMAL_STATEMENT.md); the named premises are listed in [proofs/HYPOTHESES.md](../HYPOTHESES.md).

## ⚠️ Two kinds of files

**Issue experiments (certified results).** The folders `issue7/`, `issue8/`, `issue10/`, `issue532/`, `issue567/`, `issue568/`, and `issue609/` hold paired Lean and Rocq files over the [shared finite-machine model](../complexity/README.md). They contain no `sorry`, `Admitted`, or new axioms. Their main theorems are listed in [the result manifest](../../scripts/proof_status.json), and CI checks each listed theorem's assumptions. Open problems appear only as named propositions passed as explicit theorem arguments.

**Legacy sketches (historical, not certified).** [`lean/PvsNPProofAttempt.lean`](lean/PvsNPProofAttempt.lean) and [`rocq/PvsNPProofAttempt.v`](rocq/PvsNPProofAttempt.v) define their own competing P and NP and contain axioms, `sorry`, and `Admitted`. CI compiles them, but compilation does not certify them. They are slated for archiving ([#627](https://github.com/konard/p-vs-np/issues/627)). The "Proof Strategies Explored" section below describes these sketches. Isabelle files are archived in [`../../archive/isabelle/`](../../archive/isabelle/) and are not checked.

## Index

| Folder | Topic | Certified theorems (Lean / Rocq) | Main open premise |
|---|---|---|---|
| [issue7/](issue7/README.md) | Clocked-SAT sentence behind the independence question | 15 / 15 | `SATHard` (for some directions) |
| [issue8/](issue8/README.md) | `NP ⊆ P` target; DPLL correctness and call bound | 14 / 14 | `SATHard` |
| [issue10/](issue10/README.md) | `NP ⊈ P` target; refuted enumeration and circularity arguments | 12 / 12 | `PSubsetPPoly`, `CircuitSATInNP` |
| [issue532/](issue532/RESEARCH_LOG.md) | 41 idea dossiers, `Machines`, `Circuits`, `SATVerifier` | 16 / 16 | Per idea; see the log |
| [issue567/](issue567/README.md) | Residual-key counterexample (its circuit decoder is in `issue532/…/Idea41` and counted there) | 2 / 2 | `CircuitSATInNP` |
| [issue568/](issue568/README.md) | First Cook–Levin slice: bounded machine tableaux | 5 / 5 | `SATHard` |
| [issue609/](issue609/README.md) | Corrected replacements for PR #41's P = NP sketches | 10 / 10 | `SATHard` (for the P = NP direction) |

The counts come from `scripts/proof_status.json` on `main`. The issue532 count covers only the manifest entries; its other compiled theorems are not in the manifest. Agda regression files for issue #572 live in [`../../experiments/issue572/`](../../experiments/issue572/).

## Relationship to the classical disjunction

### What We Proved in `p_vs_np_decidable/`
In the files named "decidable", we showed that:
- `(P = NP) ∨ (P ≠ NP)` holds by classical excluded middle (`Classical.em`)
- This is not decidability in the computability sense, and it gives no algorithm
- It does not tell us which side holds

### What These Experiments Attempt
These experiments try to determine **which answer is correct**, or to isolate exactly what remains open:
- Routes to P = NP through polynomial-time algorithms
- Routes to P ≠ NP through lower bounds
- Formal audits of published or proposed arguments

**Key Insight**: Knowing that `P = NP ∨ P ≠ NP` holds classically does not tell us which side holds. Excluded middle is non-constructive.

## Williams' algorithmic method

The [corrected experiment](p_not_equal_np_proof_attempt.md) records the
conditional implication from faster Circuit-SAT to `NEXP ⊄ P/poly`, its
explicit unproved premises, and the next machine-level obligation. The paired
[Lean](WilliamsFramework.lean) and [Rocq](WilliamsFramework.v) regression
files import [Idea 41](issue532/ideas/Idea41.md) instead of defining another
circuit or runtime model. No P-versus-NP separation is claimed.

[issue10/](issue10/README.md) states the issue #10 target `NP ⊈ P` and proves,
in paired Lean and Rocq files without axioms, the facts that the write-up
states informally. These are: the enumeration and circularity arguments fail,
the PR #43 cost and bound defects are real, and the certificate-length half of
`CircuitSATInNP` holds. On `main`, `CircuitSATInNP` and `PSubsetPPoly` remain
named premises. PR [#631](https://github.com/konard/p-vs-np/pull/631) proves
`CircuitSATInNP` and PR [#632](https://github.com/konard/p-vs-np/pull/632)
proves `PSubsetPPoly`; both are unmerged as of 2026-11-03.

[issue8/](issue8/README.md) states the issue #8 target `NP ⊆ P`, the opposite
direction. Its paired Lean and Rocq files prove a DPLL solver correct for the
shared SAT language, including PR #41's issue #610 regression formula, and
bound its calls by `2^(|w|+1)`, which is not polynomial. They also prove that a
polynomial `Run` bound for that solver is equivalent to `NP ⊆ P` given
`SATHard`. `SATHard` is not proved on `main`. The corrected [`NP ⊆ P` write-up](np_subset_p_proof_attempt.md)
replaces PR #41's documents and lists their corrections.

[issue568/](issue568/README.md) begins the constructive Cook–Levin bridge
over the shared machine. Its paired Lean and Rocq proofs equate locally
checked, bounded configuration traces with `Run` and bound their represented
tape span. The CNF encoding and reduction machine remain open on `main`.
PR [#630](https://github.com/konard/p-vs-np/pull/630) holds further Cook–Levin
slices; as of 2026-11-03 it is unmerged and its CI is failing.

[issue7/](issue7/README.md) states the clocked-SAT sentence behind issue #7's
independence question. Its paired Lean and Rocq files prove a clock lemma and
that the Σ⁰₂ form `∃ m p, ∀ x, clockCheck m p x = true` is `InP SAT`, with no
premise. Given `SATHard`, it is equivalent to `PEqualsNP`. Its Π⁰₂ negation
implies `PNotEqualsNP` with no premise (`pNotEqualsNP_of_pi2`); the converse
needs `SATHard`. They also prove that the per-machine quantifier order holds
outright. Nothing about ZFC provability is claimed.

Issue #567 added an executable circuit decoder for the shared `encCircuit`
format to `issue532/lean/Idea41.lean` (the Rocq `Idea41.v` already had one), with
round-trip and soundness proofs, and proves `coarseKey_not_satisfiability_complete`
in [issue567/](issue567/README.md): answers cannot be reused solely by a proposed
coarse memoization key. [issue609/](issue609/README.md)
replaces PR #41's axiom-laden sketches with axiom-free paired files.
[issue532/RESEARCH_LOG.md](issue532/RESEARCH_LOG.md) records the 41 idea
dossiers and their verdicts.

## Proof Strategies Explored

This section describes the strategies sketched in the legacy `PvsNPProofAttempt` files. The status labels refer to those sketches.

### 1. Direct Construction Approach
**Goal**: Construct a polynomial-time algorithm for an NP-complete problem (e.g., SAT)

**Status**: INCOMPLETE
- Requires explicit algorithm construction
- Must prove correctness and polynomial running time
- If successful, would prove P = NP

**Challenge**: Finding such an algorithm is the core difficulty of the problem!

### 2. Diagonalization Approach
**Goal**: Use time hierarchy theorems to separate P from NP

**Status**: INCOMPLETE
- Requires proving that some NP language cannot be decided in polynomial time
- Must show impossibility for ALL polynomial-time algorithms
- If successful, would prove P ≠ NP

**Challenge**: Proving such a strong impossibility result is extremely difficult

### 3. Oracle Separation (Relativization)
**Goal**: Use oracle-enhanced Turing machines to separate P from NP

**Status**: KNOWN TO FAIL
- Baker-Gill-Solovay (1975) proved this approach cannot work
- There exist oracles A and B where P^A = NP^A but P^B ≠ NP^B
- This means any proof of P vs NP must be "non-relativizing"

**Barrier**: Relativization barrier

### 4. Circuit Complexity Approach
**Goal**: Prove superpolynomial circuit lower bounds for an NP problem

**Status**: INCOMPLETE
- Requires proving that some NP problem needs superpolynomial-size circuits
- This is one of the hardest open problems in complexity theory
- If successful, would prove P ≠ NP (since P ⊆ P/poly)

**Challenge**: Best known circuit lower bounds are far from what's needed

### 5. Algebraic Approach (GCT)
**Goal**: Use Geometric Complexity Theory to separate complexity classes

**Status**: INCOMPLETE
- Requires deep algebraic geometry and representation theory
- Active area of research (Mulmuley, Sohoni, et al.)
- Extremely technical and not yet formalized

**Challenge**: Even the conjectures in GCT are unproven

### 6. Natural Proofs Barrier
**Goal**: Use "natural" proof techniques

**Status**: KNOWN TO FAIL (under cryptographic assumptions)
- Razborov–Rudich (1997) showed that, if strong pseudorandom functions exist, natural proofs cannot prove superpolynomial circuit lower bounds such as NP ⊄ P/poly
- Natural proofs are constructive and work for large classes of functions
- If sufficiently strong (subexponentially hard) one-way functions exist, natural proofs cannot prove NP ⊄ P/poly

**Barrier**: Natural proofs barrier

## Known Barriers

Three major barriers to proving P vs NP:

### 1. Relativization (Baker-Gill-Solovay, 1975)
- Oracle-based proofs don't work
- Any proof must use non-relativizing techniques

### 2. Natural Proofs (Razborov-Rudich, 1997)
- "Natural" circuit lower bound techniques are blocked
- Assumes existence of cryptographically strong one-way functions

### 3. Algebrization (Aaronson-Wigderson, 2008)
- Extension of relativization to algebraic computation
- Rules out even more proof techniques

**Implication**: Any successful proof of P vs NP must avoid ALL three barriers!

## File Structure

```
proofs/experiments/
├── README.md (this file)
├── p_not_equal_np_proof_attempt.md   # Williams-method write-up (issue #10 side)
├── np_subset_p_proof_attempt.md      # NP ⊆ P write-up (issue #8 side)
├── WilliamsFramework.lean / .v       # Axiom-free regression files over Idea 41
├── issue7/  issue8/  issue10/        # Certified issue experiments (lean/, rocq/, README.md)
├── issue532/                         # 41 idea dossiers, RESEARCH_LOG.md, lean/, rocq/
├── issue567/  issue568/  issue609/   # Certified issue experiments (lean/, rocq/, README.md)
├── lean/
│   └── PvsNPProofAttempt.lean        # Legacy sketch: axioms and sorry
└── rocq/
    └── PvsNPProofAttempt.v           # Legacy sketch: Axiom and Admitted
```

The legacy `PvsNPProofAttempt` files contain:
- Their own definitions of complexity classes (P, NP, NP-complete), separate from the shared model
- Formalization of different proof strategies
- Documentation of why each strategy is challenging
- Axioms and incomplete proofs (with `sorry`/`Admitted`) standing for proof obligations

## What Would a Complete Proof Require?

### For P = NP:
1. An explicit polynomial-time algorithm for an NP-complete problem
2. Proof of correctness: algorithm solves the problem
3. Proof of efficiency: algorithm runs in polynomial time
4. Verification that this implies all NP problems are in P

### For P ≠ NP:
1. A specific language in NP (it need not be NP-complete; see `test_existence_of_hard_problem` in [`../p_not_equal_np/`](../p_not_equal_np/README.md))
2. Proof that it is in NP
3. Proof that NO polynomial-time algorithm decides it
4. This requires proving a universal negative statement (very hard!)

## Why This is So Hard

1. **Proving positive results (P = NP)**:
   - Requires finding a clever algorithm
   - Possibly discoverable by insight or machine search
   - But no one has found such an algorithm in 50+ years

2. **Proving negative results (P ≠ NP)**:
   - Requires proving a universal impossibility
   - Must rule out ALL possible polynomial-time algorithms
   - Known barriers eliminate many proof techniques

3. **Fundamental difficulty**:
   - The problem asks about the limits of efficient computation
   - It's asking "are there fundamentally hard problems?"
   - This is both a mathematical and philosophical question

## Educational Value

These experiments demonstrate:

1. **Difference between the classical disjunction and a solution**
   - Classical logic gives `P = NP ∨ P ≠ NP` (excluded middle, not algorithmic decidability)
   - We don't know WHICH side holds

2. **Proof barriers in complexity theory**
   - Not all proof strategies can work
   - Understanding barriers guides future research

3. **Formalization challenges**
   - Even expressing what a proof would require is non-trivial
   - Formal verification requires making intuitions precise

4. **Limits of current knowledge**
   - In the legacy sketches, `sorry`/`Admitted` mark what is not known; the issue experiments use named premises instead
   - Transparency about incomplete proofs is scientifically valuable

## Verification

CI compiles the Lean and Rocq files in this directory. Compilation checks type-correctness only:
- ✅ All files type-check and compile
- ✅ Theorems listed in [the result manifest](../../scripts/proof_status.json) have no assumptions beyond the listed logical axioms; CI checks this with `#print axioms` and `Print Assumptions`
- ⚠️ The legacy `PvsNPProofAttempt` files are compiled but not certified; they contain axioms and admissions
- ⚠️ CI does not check that a definition matches its informal intent; that is a matter for review

No file here proves P = NP or P ≠ NP.

## Conclusion

These experiments show that:
- `P = NP ∨ P ≠ NP` holds by classical excluded middle (this is not algorithmic decidability)
- We can **formalize** what a proof would look like
- Multiple **barriers** prevent many natural approaches
- The problem remains **unsolved** despite decades of effort

The gap between the classical disjunction and knowing which side holds is the essence of the Millennium Problem.

## References

- Baker, T., Gill, J., & Solovay, R. (1975). Relativizations of the P =? NP Question.
- Razborov, A. A., & Rudich, S. (1997). Natural Proofs.
- Aaronson, S., & Wigderson, A. (2008). Algebrization: A New Barrier in Complexity Theory.
- Cook, S. (1971). The Complexity of Theorem-Proving Procedures.
- Mulmuley, K., & Sohoni, M. (2001). Geometric Complexity Theory I.
