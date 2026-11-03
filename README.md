# P vs NP: Research Repository

**Language:** [English](README.md) | [Русский (Russian)](README.ru.md)

---

**A research repository with educational background material**

*Last Updated: November 2026*

This repository studies the P versus NP problem, one of the seven Clay Mathematics Institute Millennium Prize Problems. It holds machine-checked definitions and partial results in Lean and Rocq, together with educational background documents. It does not claim a resolution of P versus NP.

## 🧭 Start here (reading order)

1. [README.md](README.md): this overview.
2. [FORMAL_STATEMENT.md](FORMAL_STATEMENT.md): the Clay statement, its formal target, the modeling choices, the result graph, and what counts as solved.
3. [proofs/complexity/README.md](proofs/complexity/README.md): the shared finite-machine model.
4. [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md): every named premise that is used but not proved.
5. [CLAIMS.md](CLAIMS.md): the ledger of checkable claims made by these documents, with the check behind each and the queue of statements still to formalize.
6. [RESEARCH_VISION.md](RESEARCH_VISION.md): how research is done here.
7. [ROADMAP.md](ROADMAP.md): the operative plan.
8. [RESEARCH_LOG.md](proofs/experiments/issue532/RESEARCH_LOG.md): the 41 idea dossiers and their verdicts.
9. [proofs/attempts/COMMON_ERRORS.md](proofs/attempts/COMMON_ERRORS.md): recurring errors in historical attempts.
10. Background: [P_VS_NP_TASK_DESCRIPTION.md](P_VS_NP_TASK_DESCRIPTION.md), [TOOLS_AND_METHODOLOGIES.md](TOOLS_AND_METHODOLOGIES.md), and the [literature registry](literature/README.md).
11. [CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md) (also [CLAUDE.md](CLAUDE.md)): contributor and agent instructions.

## 🎯 Current formalization scope

The formal target is `Complexity.PEqualsNP` (every language in NP is in P) in the repository's [finite-machine model](proofs/complexity/README.md). [FORMAL_STATEMENT.md](FORMAL_STATEMENT.md) relates it to the Clay statement. The model's programs are finite instruction tables, costs count actual transitions, and NP certificates have polynomial length bounds. Equivalence of this implementation to every conventional machine model has not been formalized here.

On `main`, [the result manifest](scripts/proof_status.json) certifies 78 Lean and 78 Rocq theorems. The status of the main statements is:

| Statement | Status on `main` | Formal name |
|---|---|---|
| P ⊆ NP | **Proved** for this model. The proof turns a P machine into a verifier that ignores its certificate. | `Complexity.pSubsetNP` |
| SAT ∈ NP | **Proved** with an explicit 45-state verifier. | `Issue532.SATVerifier.satInNP` |
| SAT is NP-hard (Cook–Levin hardness) | **Open named premise.** The first Cook–Levin slice (bounded machine tableaux) is proved. | `SATHard`, `CookLevin`; slice in `Issue568.Tableau` |
| CircuitSAT ∈ NP | Premise on `main`. Proved in PR [#631](https://github.com/konard/p-vs-np/pull/631), unmerged as of 2026-11-03. | `CircuitSATInNP` |
| P ⊆ P/poly | Premise on `main`. Proved in PR [#632](https://github.com/konard/p-vs-np/pull/632), unmerged as of 2026-11-03. | `PSubsetPPoly` |
| P = NP ∨ P ≠ NP | Proved by classical excluded middle. It is not an algorithm and decides neither side. | `PvsNPDecidable.P_vs_NP_is_decidable` |
| P = NP, P ≠ NP, independence, any superpolynomial lower bound | **Not proved.** | |

Named premises are explicit theorem arguments, never axioms. `SATHard` is the main open bridge. Without it, "SAT ∈ P" and "P = NP" are different formal statements here: `P = NP → SAT ∈ P` is proved, while the converse needs `SATHard`. The full list of premises is in [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md).

Other certified results on `main` include the Π⁰₂ clocked-SAT bridge to `P ≠ NP`, which needs no premise (`Issue7.ClockedSAT.pNotEqualsNP_of_pi2`); a correct DPLL solver with a `2^(|w|+1)` call bound ([issue8](proofs/experiments/issue8/README.md)); an executable Lean decoder and certificate checker for the shared circuit encoding (`Issue532.Idea41`, added for issue #567; the Rocq decoder predates it); and the residual-key counterexample `coarseKey_not_satisfiability_complete` ([issue567](proofs/experiments/issue567/README.md)).

The [41 idea dossiers](proofs/experiments/issue532/RESEARCH_LOG.md) record a verdict for each idea; most of their theorems are conditional, and most are not certified results. Only 7 dossier theorems per prover (1 from Idea 01, 6 from Idea 41) are in the manifest, among its 16 issue532 rows. The dossier checker `experiments/issue532/check_dossiers.py` scans their Lean and Rocq files for admissions and axioms, and 24 of the 41 ideas have vacuity regressions in [experiments/issue532_vacuity/](experiments/issue532_vacuity/).

See the P ⊆ NP proofs:
- [Shared model, Lean](proofs/complexity/lean/Complexity.lean) and [Rocq](proofs/complexity/rocq/Complexity.v)
- [Lean 4 proof](proofs/p_vs_np_decidable/lean/PSubsetNP.lean)
- [Rocq proof](proofs/p_vs_np_decidable/rocq/PSubsetNP.v)
- [Agda proof](proofs/p_vs_np_decidable/agda/PSubsetNP.agda)
- [Detailed documentation](proofs/p_vs_np_decidable/README.md)

> **Note:** Isabelle/HOL proofs have been archived to [`./archive/isabelle/`](archive/isabelle/) and are not checked. CI checks Lean 4 (`leanprover/lean4:v4.34.1`, from [`lean-toolchain`](lean-toolchain)), Rocq 9.0 (`rocq/rocq-prover:9.0`, from [the workflow](.github/workflows/verification.yml)), and the listed shared-model Agda files in a pinned Agda image. The Lean code uses core Lean only; Mathlib is not used.

**❓ THE QUESTION: Is NP ⊆ P true?**

For P = NP to be true, we need **both**:
1. P ⊆ NP (proved in the stated finite-machine model)
2. NP ⊆ P (❓ **unknown**)

The remaining question is whether every language in NP also belongs to P. The classical statement `P = NP ∨ P ≠ NP` does not decide which side holds.

**Model warning:** The older P=NP example in [`proofs/p_eq_np/`](proofs/p_eq_np/README.md), the legacy `PvsNPProofAttempt` files in [`proofs/experiments/`](proofs/experiments/README.md), and the archived Isabelle files use separate toy encodings with their own competing P and NP definitions. The legacy Lean and Rocq files still contain axioms, `Admitted`, or `sorry`, and are not certified. Their results must not be read as statements about the finite-machine P and NP definitions above or the Clay problem. Issue [#627](https://github.com/konard/p-vs-np/issues/627) proposes archiving them.

## Overview

The P versus NP problem asks whether every problem whose solution can be quickly verified (NP) can also be quickly solved (P). This is one of the most important open questions in mathematics and computer science, with a $1 million prize for its resolution.

## Repository Contents

### 🧭 Formal Status and Research Process

- **[FORMAL_STATEMENT.md](FORMAL_STATEMENT.md)** - The Clay statement and its formal target, modeling choices, result graph, and what counts as solved
- **[proofs/HYPOTHESES.md](proofs/HYPOTHESES.md)** - Manifest of named premises that are used but not proved
- **[CLAIMS.md](CLAIMS.md)** - Ledger of checkable claims (formal, conditional, script, source) and the formalization queue; checked by `scripts/check_claims.py`
- **[RESEARCH_VISION.md](RESEARCH_VISION.md)** - How research is done in this repository
- **[ROADMAP.md](ROADMAP.md)** - Operative plan and next milestones
- **[literature/README.md](literature/README.md)** - Literature registry ([REGISTRY.md](literature/REGISTRY.md), [registry.json](literature/registry.json)) and the [claimed proofs from 2017 to 2026](literature/CLAIMED_PROOFS_2017_2026.md) not yet in the attempts catalog
- **[CONTRIBUTING.md](CONTRIBUTING.md)** and **[AGENTS.md](AGENTS.md)** / **[CLAUDE.md](CLAUDE.md)** - Contributor and agent instructions
- **[scripts/](scripts/README.md)** - Checks, including [`check_proof_status.py`](scripts/check_proof_status.py), [`check_formal_statement.py`](scripts/check_formal_statement.py), and [`check_literature_registry.py`](scripts/check_literature_registry.py)

### 📘 Core Documentation

1. **[P_VS_NP_TASK_DESCRIPTION.md](P_VS_NP_TASK_DESCRIPTION.md)** - Comprehensive, scientifically rigorous description of the P vs NP problem
   - Formal problem statement and definitions
   - Historical context and importance
   - NP-completeness theory
   - Current state of knowledge
   - Proof approaches and techniques
   - Related complexity classes
   - Practical implications

2. **[TOOLS_AND_METHODOLOGIES.md](TOOLS_AND_METHODOLOGIES.md)** - Complete catalog of tools, techniques, and resources
   - Theoretical foundations and computational models
   - Mathematical tools (combinatorics, algebra, logic, probability)
   - Proof techniques (diagonalization, circuit lower bounds, barriers)
   - Computational tools (SAT solvers, proof assistants, symbolic computation)
   - Research methodologies
   - Specific research programs (GCT, proof complexity, derandomization)

3. **[DETAILED_SOLUTION_PLAN.md](DETAILED_SOLUTION_PLAN.md)** - Multi-phase research plan for approaching the problem
   - Phase 1: Foundation building (6 months)
   - Phase 2: Specialization and deep dive (6 months)
   - Phase 3: Original research (12+ months)
   - Phase 4: Advanced research directions
   - Phase 5: Integration and synthesis
   - Specific tactics and best practices
   - Milestones and evaluation criteria

4. **[SOLUTION_STRATEGIES.md](SOLUTION_STRATEGIES.md)** - Catalog of 20 solution strategies for formal testing and progress on P vs NP
   - Formal verification frameworks (6 strategies)
   - Barrier-aware approaches (3 strategies)
   - Incremental progress strategies (6 strategies)
   - Novel and interdisciplinary approaches (5 strategies)
   - Strategy integration matrix and implementation priorities
   - Recommended roadmap with realistic timelines and success metrics

5. **[SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md](SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md)** - Comprehensive catalog of formal solution strategies
   - Direct classical logic approaches (law of excluded middle, proof by contradiction)
   - Constructive and intuitionistic approaches (proof search, realizability)
   - Model-theoretic strategies (standard models, forcing, independence)
   - Proof-theoretic strategies (provability, Gödel's theorems, reverse mathematics)
   - Computational logic approaches (ATP, SAT/SMT solving, proof assistants)
   - Meta-mathematical strategies (arithmetical hierarchy, definability, category theory)
   - Formalization strategies (multi-proof-assistant verification, modular design)
   - Indirect approaches via related problems
   - Hybrid and interdisciplinary strategies
   - Implementation roadmap with concrete milestones

6. **[P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md)** - Comprehensive list of potential solution strategies for proving P ≠ NP
   - Circuit complexity approaches (general circuits, monotone, bounded-depth, arithmetic)
   - Algebraic methods (GCT, Valiant's model, algebraic independence)
   - Algorithm-to-lower-bound techniques (Williams' framework, SAT algorithms)
   - Proof complexity approaches (super-polynomial proofs, resolution, algebraic systems)
   - Communication complexity methods
   - Derandomization and pseudorandomness connections
   - Structural and indirect approaches
   - Novel interdisciplinary methods (quantum, statistical physics, topology)
   - Meta-complexity and conditional results
   - Restricted models and special cases

7. **[P_VS_NP_INDEPENDENCE_STRATEGIES.md](P_VS_NP_INDEPENDENCE_STRATEGIES.md)** - Solution strategies for testing P vs NP independence
   - Theoretical foundations of independence and undecidability
   - 30+ strategies across 6 major categories (logical, proof-theoretic, algorithmic, empirical, interdisciplinary, hybrid)
   - Analysis of Shoenfield absoluteness and its implications
   - Practical research plans and formalization approaches
   - Realistic assessments and expected outcomes
   - Comprehensive references for logic, set theory, and complexity theory

### 📄 Reference Materials

- **[pvsnp.pdf](pvsnp.pdf)** - Official problem description by Stephen Cook from Clay Mathematics Institute

### 🔬 Formal Verification

The repository includes formal verification frameworks in multiple proof assistants (Lean 4, Rocq, and Agda) organized into the following categories:

> **Note:** Isabelle/HOL support has been sunset. Existing Isabelle proofs are archived in [`./archive/isabelle/`](archive/isabelle/) for reference.

#### Tutorial Proofs for Learning Proof Assistants (`proofs/basic/`)
Bootstrap proof files demonstrating foundational formal verification concepts and serving as templates:
- **[proofs/basic/lean/Basic.lean](proofs/basic/lean/Basic.lean)** - Lean 4 foundational proofs
- **[proofs/basic/rocq/Basic.v](proofs/basic/rocq/Basic.v)** - Rocq foundational proofs
- **[proofs/basic/agda/Basic.agda](proofs/basic/agda/Basic.agda)** - Agda foundational proofs

These files serve as tutorials for researchers learning to use proof assistants and provide CI validation that the formal verification infrastructure is working correctly.

#### Advanced Proof Frameworks for P vs NP
The repository contains four distinct proof frameworks exploring different aspects of the P vs NP problem:

1. **[P = NP Formalization](proofs/p_eq_np/README.md)** (`proofs/p_eq_np/`)
   - Legacy toy-model framework for hypothetical P=NP claims; it does not use the shared machine semantics and defines its own P and NP
   - Its examples and tests do not establish the Clay P versus NP statement
   - The Lean file has 4 axioms and the Rocq file has 3 `Admitted` and 1 `Axiom`; CI compiles them but does not certify them. The Agda file uses postulates and is not checked by CI
   - Slated for archiving ([#627](https://github.com/konard/p-vs-np/issues/627))

2. **[P ≠ NP Formalization](proofs/p_not_equal_np/)** (`proofs/p_not_equal_np/`)
   - Conditional criteria for proofs that P does not equal NP in the shared machine model
   - See [detailed documentation](proofs/p_not_equal_np/README.md)
   - SAT ∈ NP is proved (`Issue532.SATVerifier.satInNP`); NP-hardness of SAT (`SATHard`) remains a named premise
   - Available in Lean, Rocq, and Agda

3. **[P ⊆ NP Formal Proof & Classical Tautology](proofs/p_vs_np_decidable/)** (`proofs/p_vs_np_decidable/`)
   - **Contains the P ⊆ NP proof for the finite-machine model** ([detailed documentation](proofs/p_vs_np_decidable/README.md))
   - Formalizes that P vs NP has a definite answer in classical logic via law of excluded middle
   - See [detailed documentation](proofs/p_vs_np_decidable/README.md)
   - **Note:** "Decidable" here means the classical tautology that (P=NP) ∨ (P≠NP) holds, NOT algorithmic decidability
   - **The key question:** Does NP ⊆ P hold?
   - Available in Lean, Rocq, and Agda

4. **[Possible Independence from ZFC](proofs/p_vs_np_undecidable/)** (`proofs/p_vs_np_undecidable/`)
   - Conditional schema for an explicitly supplied proof relation; no ZFC independence result is claimed
   - See [detailed documentation](proofs/p_vs_np_undecidable/README.md)
   - Explores whether P vs NP could be independent of standard axiom systems
   - Available in Lean, Rocq, and Agda

#### Historical P vs NP Proof Attempts (`proofs/attempts/`)

The [attempts catalog](proofs/attempts/README.md) has 116 folders (63 claiming P = NP, 50 claiming P ≠ NP, 3 other) taken from [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), dated 1986 to 2016. Most entries are historical sketches. The [coverage index](proofs/attempts/COMMON_ERRORS.md#attempt-coverage-index) rates only 2 as mechanized concrete refutations ([Gubin 2010](proofs/attempts/sergey-gubin-2010-peqnp/README.md) and [Zhu 2007](proofs/attempts/guohun-zhu-2007-peqnp/README.md)). Of the others, 2 are conditional results, 1 is an identified gap, and 111 are informal analyses. Claimed proofs after 2016 are tracked in [literature/CLAIMED_PROOFS_2017_2026.md](literature/CLAIMED_PROOFS_2017_2026.md). The work order for raising these evidence levels is [proofs/attempts/REFUTATION_PLAN.md](proofs/attempts/REFUTATION_PLAN.md).

1. **[Ted Swart (1986/87) - P=NP via Linear Programming](proofs/attempts/ted-swart-1986-87-peqnp/)** (`proofs/attempts/ted-swart-1986-87-peqnp/`)
   - Entry #1 on [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
   - Claimed polynomial-size LP formulations for Hamiltonian cycle
   - The published refutation is Yannakakis' theorem (STOC 1988; JCSS 1991): symmetric LP formulations of the TSP polytope require exponential size
   - The local folder is an informal analysis, not a mechanized refutation; see [detailed documentation](proofs/attempts/ted-swart-1986-87-peqnp/README.md)
   - Historical Lean and Rocq sketches, not certified

Lean and Rocq files and the shared-model Agda files are checked by GitHub Actions. The other Agda files and archived Isabelle files are historical examples outside this CI check. [![Formal Verification Suite](https://github.com/konard/p-vs-np/actions/workflows/verification.yml/badge.svg)](https://github.com/konard/p-vs-np/actions/workflows/verification.yml)

**What the badge means:** On `main`, CI compiles the Lean and Rocq sources and checks only the listed shared-model Agda files. Compilation accepts `sorry`, `Admitted`, and axioms, so it does not certify every theorem in those files. Pull requests run the prover jobs selected by changed files; a skipped job provides no proof check for that PR.

| Status | Scope | Guarantee |
|---|---|---|
| Certified result | The specific Lean and Rocq conclusions in [the result manifest](scripts/proof_status.json) | CI scans each source and its local imports for admissions and unproved declarations, then checks `#print axioms` or `Print Assumptions` against the listed allowed logical axioms. The claim still has only the scope of its formal model and explicit theorem premises. |
| Historical sketch | The [attempt catalog](proofs/attempts/ATTEMPTS.md) and other unlisted formalizations | CI may compile the file, but admissions and assumptions may remain. A `refutation/` path alone does not mean its conclusion is proved. |
| Outside current check | Other Agda files and archived Isabelle files | The workflow does not check them. |

For the audited conclusions, run `python3 scripts/check_proof_status.py` for the source boundary, then `python3 scripts/check_proof_status.py --lean` or `--rocq` after building the corresponding prover files. The manifest states every approved assumption by name. No certified conclusion establishes P = NP or P ≠ NP.

## Key Highlights

### Problem Significance

- **Cryptography:** Many cryptographic schemes rely on *average-case* hardness of specific problems (factoring, discrete logarithm, lattice problems). A constructive proof that **P = NP** with practical algorithms would break most standard public-key cryptosystems, but **P ≠ NP** alone does not guarantee the existence of one-way functions or secure cryptography. **Note on one-way functions (OWFs):** Existence of OWFs would imply P ≠ NP, but P ≠ NP alone does **not** imply OWFs exist; the converse direction is unknown. This is because P ≠ NP only establishes worst-case hardness for some problems, while cryptography requires average-case hardness.
- **Optimization:** Thousands of real-world problems are NP-complete
- **Mathematics:** P = NP would enable automated theorem proving
- **Artificial Intelligence:** Impacts machine learning and automated reasoning

### Current Consensus

- **Most Believed:** P ≠ NP (problems exist that can be verified but not efficiently solved)
- **Major Barriers:**
  - **Relativization** ([Baker, Gill, Solovay, 1975](https://doi.org/10.1137/0204037)): Techniques that work in all oracle worlds cannot resolve P vs NP
  - **Natural Proofs** ([Razborov, Rudich, 1997](https://doi.org/10.1006/jcss.1997.1494)): Under cryptographic assumptions, "natural" techniques cannot prove super-polynomial circuit lower bounds
  - **Algebrization** ([Aaronson, Wigderson, STOC 2008](https://doi.org/10.1145/1374376.1374481)): Extends relativization and arithmetization barriers, showing further limitations
- **Best Known Algorithms:**
  - **2-SAT:** O(n + m) via implication graph + strongly connected components ([Aspvall, Plass, Tarjan, 1979](https://doi.org/10.1016/0020-0190(79)90002-4))
  - **3-SAT:** ~O(1.307^n), randomized. PPSZ (Paturi, Pudlák, Saks, Zane 2005); [Hertli 2014](https://doi.org/10.1137/120868177) showed its Unique-3-SAT bound holds for general 3-SAT; biased PPSZ gives 1.306995^n ([Hansen, Kaplan, Zamir, Zwick, STOC 2019](https://doi.org/10.1145/3313276.3316359)). Deterministic: 1.32793^n ([Liu, ICALP 2018](https://doi.org/10.4230/LIPIcs.ICALP.2018.88)); the derandomized Schöning algorithm gives (4/3 + ε)^n ([Moser, Scheder, STOC 2011](https://doi.org/10.1145/1993636.1993670)). These are the best peer-reviewed bounds; unreviewed October 2026 claims of 2^{o(n)}-time algorithms (claims that ETH is false) are listed under [Recent developments](#recent-developments-20242026)
  - **k-SAT (k≥4):** Base depends on k (PPSZ variants)
  - **General CNF-SAT:** Bounds depend on clause structure
- **Best Lower Bounds:**
  - **General circuits (full binary basis):** ~3.1·n − o(n) gates for explicit functions (Li & Yang, STOC 2022)
    - Prior record: (3 + 1/86)·n − o(n) (Find, Golovnev, Hirsch, Kulikov, FOCS 2016)
  - **Restricted models:** Exponential bounds for monotone circuits, AC⁰, etc.
  - Still far from the super-polynomial bounds needed for P ≠ NP

### Notable Results

- **1971:** Cook proves SAT is NP-complete
- **1972:** Karp identifies 21 NP-complete problems
- **1985:** Razborov proves superpolynomial (n^{Ω(log n)}) monotone circuit lower bounds for CLIQUE; Andreev (1985) and Alon and Boppana ([1987](https://doi.org/10.1007/BF02579196)) make monotone bounds exponential
- **1997:** Razborov-Rudich identify Natural Proofs barrier
- **2011:** Williams proves NEXP ⊄ ACC⁰ ([Williams, CCC 2011; J. ACM 2014](https://doi.org/10.1145/2559903)) - a non-relativizing result using an algorithm-to-lower-bound connection
- **2025:** Advances in circuit lower bounds, including:
  - Superpolynomial lower bounds against constant-depth algebraic circuits (Limaye, Srinivasan, Tavenas, FOCS 2021; [J. ACM 2025](https://doi.org/10.1145/3734215))
  - Quantum circuit lower bounds in the magic hierarchy, showing state preparation limits (Parham 2025, [arXiv:2504.19966](https://arxiv.org/abs/2504.19966))

### Recent developments (2024–2026)

These items are dated and hedged. None of them settles P versus NP. The [literature registry](literature/REGISTRY.md) records sources and their review status.

- **2024–2025, peer-reviewed:** Williams showed TIME[t] ⊆ SPACE[√(t log t)] for multitape machines ([STOC 2025](https://doi.org/10.1145/3717823.3718225)), building on the Cook–Mertz tree-evaluation algorithm ([STOC 2024](https://doi.org/10.1145/3618260.3649664)). Chen, Hirahara, and Ren ([STOC 2024](https://doi.org/10.1145/3618260.3649624)) proved near-maximum circuit lower bounds for symmetric exponential time with one bit of advice (S₂E/1), and Li ([STOC 2024](https://doi.org/10.1145/3618260.3649615)) removed the advice (S₂E).
- **6 October 2026, unreviewed:** the [openai/math](https://github.com/openai/math) release had 722 manuscripts in 372 families; at commit `4eaee87` (2026-10-30) the catalogue lists 721 manuscripts in 373 families. The release included some Lean-checked restricted lower bounds in its own machine model, and a claimed proof of the Unique Games Conjecture; 3 manuscripts were reportedly withdrawn.
- **26–27 October 2026, unreviewed:** OpenAI and Anthropic published claims that the Exponential Time Hypothesis (ETH) is false, each backed by a Lean-checked k-SAT running-time theorem in its own machine model (Anthropic's development also defines ETH and proves `ethIsFalse`; OpenAI's does not define ETH). Impagliazzo, Paturi and Williams are reviewing the OpenAI claim; no outside review of the Anthropic claim is announced as of 2026-11-03. ETH is at least as strong as P ≠ NP: ETH implies P ≠ NP, and the converse is unknown. If the claims hold, they do not settle P vs NP; refuting ETH is not known to imply P = NP. Draft PR [#639](https://github.com/konard/p-vs-np/pull/639) (unmerged as of 2026-11-03) formalizes ETH and SETH; no certified file here uses ETH or SETH as a premise.

## Getting Started

### For Researchers

1. Follow the [reading order](#-start-here-reading-order) above, starting with [FORMAL_STATEMENT.md](FORMAL_STATEMENT.md)
2. Read [P_VS_NP_TASK_DESCRIPTION.md](P_VS_NP_TASK_DESCRIPTION.md) for comprehensive background
3. Study [TOOLS_AND_METHODOLOGIES.md](TOOLS_AND_METHODOLOGIES.md) to understand available techniques
4. Use [ROADMAP.md](ROADMAP.md) for the current plan; [DETAILED_SOLUTION_PLAN.md](DETAILED_SOLUTION_PLAN.md) is a generic multi-phase study plan

### Recommended Prerequisites

- Strong background in theoretical computer science
- Understanding of algorithms and data structures
- Mathematical maturity (discrete math, logic, algebra)
- Familiarity with complexity theory basics

### Essential Resources

**Textbooks:**
- Arora & Barak: "Computational Complexity: A Modern Approach"
- Sipser: "Introduction to the Theory of Computation"
- Papadimitriou: "Computational Complexity"

**Conferences:**
- STOC (Symposium on Theory of Computing)
- FOCS (Foundations of Computer Science)
- CCC (Computational Complexity Conference)

## Warning

The P vs NP problem has resisted 50+ years of attempts by brilliant researchers. Many false proofs have been proposed. Any attempt to solve this problem should:

- Account for known barriers (relativization, natural proofs)
- Use rigorous formal proofs
- Seek extensive peer review
- Be prepared for long-term effort
- Consider working on related, more tractable problems first

## Contributing

This is a research repository with educational background material. Read [CONTRIBUTING.md](CONTRIBUTING.md) first; automated agents also follow [AGENTS.md](AGENTS.md). Contributions welcome:
- Additional references and resources
- Updates on recent results
- Corrections or clarifications
- Alternative perspectives and approaches

## License

The Unlicense - See [LICENSE](LICENSE)

## References

- Clay Mathematics Institute: https://www.claymath.org/millennium/p-vs-np/
- Official Problem Statement PDF: https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf
- Complexity Zoo: https://complexityzoo.net/
- ECCC (Electronic Colloquium on Computational Complexity): https://eccc.weizmann.ac.il/

## Acknowledgments

Based on Stephen Cook's official problem description and extensive research in computational complexity theory spanning five decades of work by the theoretical computer science community.

## Documentation Navigation

### Formal Status and Process
- [FORMAL_STATEMENT.md](FORMAL_STATEMENT.md) - Clay statement, formal target, modeling choices, and what counts as solved
- [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md) - Named premises used but not proved
- [CLAIMS.md](CLAIMS.md) - Ledger of checkable claims and the formalization queue
- [RESEARCH_VISION.md](RESEARCH_VISION.md) - How research is done here
- [ROADMAP.md](ROADMAP.md) - Operative plan
- [RESEARCH_LOG.md](proofs/experiments/issue532/RESEARCH_LOG.md) - The 41 idea dossiers and their verdicts
- [Literature registry](literature/README.md) - [REGISTRY.md](literature/REGISTRY.md), [registry.json](literature/registry.json), and [claimed proofs 2017-2026](literature/CLAIMED_PROOFS_2017_2026.md)
- [CONTRIBUTING.md](CONTRIBUTING.md), [AGENTS.md](AGENTS.md), [CLAUDE.md](CLAUDE.md) - Contributor and agent instructions
- [scripts/README.md](scripts/README.md) - Certification and consistency checks

### Core Documentation
- [README.md](README.md) - This file (repository overview)
- [P_VS_NP_TASK_DESCRIPTION.md](P_VS_NP_TASK_DESCRIPTION.md) - Comprehensive problem description
- [TOOLS_AND_METHODOLOGIES.md](TOOLS_AND_METHODOLOGIES.md) - Tools, techniques, and resources
- [DETAILED_SOLUTION_PLAN.md](DETAILED_SOLUTION_PLAN.md) - Multi-phase research plan
- [SOLUTION_STRATEGIES.md](SOLUTION_STRATEGIES.md) - Catalog of 20 solution strategies for formal testing
- [SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md](SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md) - Solution strategies for decidability testing
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Catalog of solution strategies for P ≠ NP
- [P_VS_NP_INDEPENDENCE_STRATEGIES.md](P_VS_NP_INDEPENDENCE_STRATEGIES.md) - Solution strategies for testing independence
- [PROVING_P_VS_NP_UNDECIDABILITY.md](PROVING_P_VS_NP_UNDECIDABILITY.md) - Research roadmap for investigating independence with explicit proof obligations

### Formal Verification Documentation
- [Shared Complexity Model](proofs/complexity/README.md) - The finite-machine P and NP definitions used by the current proofs
- [Proof Experiments](proofs/experiments/README.md) - Issue experiments (issue7, issue8, issue10, issue532, issue567, issue568, issue609) and legacy sketches
- [Basic Proofs](proofs/basic/) - Foundational proofs in multiple proof assistants
- [P = NP Framework](proofs/p_eq_np/README.md) - Legacy toy model with axioms, slated for archiving
- [P ≠ NP Framework](proofs/p_not_equal_np/README.md) - Framework for verifying P ≠ NP proofs
- [Classical Tautology](proofs/p_vs_np_decidable/README.md) - Formalization that (P=NP) ∨ (P≠NP) holds in classical logic
- [Possible Independence from ZFC](proofs/p_vs_np_undecidable/README.md) - Framework for meta-mathematical independence reasoning
- [Historical Proof Attempts](proofs/attempts/README.md) - Analyses of 116 claimed P vs NP proofs, mostly informal
  - [Common errors and coverage index](proofs/attempts/COMMON_ERRORS.md) - Error families and evidence level per attempt
  - [Ted Swart (1986/87)](proofs/attempts/ted-swart-1986-87-peqnp/README.md) - P=NP via linear programming; the published refutation is Yannakakis' theorem, and the local analysis is informal
- [Archive](archive/README.md) - Archived Isabelle files, not checked by CI

All documents are interlinked - you can navigate between them using hyperlinks within each file.

---

**Important Notes:**
- This is a research repository with educational background material. It does not claim a resolution of P vs NP.
- The goal is to advance understanding, develop research skills, and contribute to complexity theory, not to claim a solution to P vs NP on a fixed timeline.
- Resolving P vs NP likely requires fundamentally new mathematical insights beyond currently known techniques.
- Any claimed proof must address known barriers (relativization, natural proofs, algebrization) and undergo rigorous peer review.
