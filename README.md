# P vs NP: Educational Research Repository

**Language:** [English](README.md) | [Русский (Russian)](README.ru.md)

---

**An Educational Resource for Researchers and Students**

*Last Updated: November 2025*

This repository contains extensive educational documentation for studying the P versus NP problem, one of the seven Clay Mathematics Institute Millennium Prize Problems.

## 🎯 Key Insight: Reframing the Problem

**✅ PROVEN: P ⊆ NP** — Every problem solvable in polynomial time is also verifiable in polynomial time.

See formal proofs in four proof assistants:
- [Lean 4 proof](proofs/p_vs_np_decidable/lean/PSubsetNP.lean)
- [Rocq proof](proofs/p_vs_np_decidable/rocq/PSubsetNP.v)
- [Isabelle/HOL proof](proofs/p_vs_np_decidable/isabelle/PSubsetNP.thy)
- [Agda proof](proofs/p_vs_np_decidable/agda/PSubsetNP.agda)
- [Detailed documentation](proofs/p_vs_np_decidable/README.md)

**❓ THE QUESTION: Is NP ⊆ P true?**

For P = NP to be true, we need **both**:
1. P ⊆ NP (✅ **proven**)
2. NP ⊆ P (❓ **unknown**)

Therefore: **P vs NP is provable/unprovable if and only if NP ⊆ P is provable/unprovable.**

This framing clarifies that the entire P vs NP question reduces to determining whether every polynomial-time verifiable problem is also polynomial-time solvable.

## Overview

The P versus NP problem asks whether every problem whose solution can be quickly verified (NP) can also be quickly solved (P). This is one of the most important open questions in mathematics and computer science, with a $1 million prize for its resolution.

## Repository Contents

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
   - Specific tactics and best practices
   - Milestones and evaluation criteria

4. **[SOLUTION_STRATEGIES.md](SOLUTION_STRATEGIES.md)** - Comprehensive catalog of 17 solution strategies for formal testing and progress on P vs NP
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

The repository includes formal verification frameworks in multiple proof assistants (Lean 4, Rocq, Isabelle/HOL, and Agda) organized into the following categories:

#### Tutorial Proofs for Learning Proof Assistants (`proofs/basic/`)
Bootstrap proof files demonstrating foundational formal verification concepts and serving as templates:
- **[proofs/basic/lean/Basic.lean](proofs/basic/lean/Basic.lean)** - Lean 4 foundational proofs
- **[proofs/basic/rocq/Basic.v](proofs/basic/rocq/Basic.v)** - Rocq foundational proofs
- **[proofs/basic/isabelle/Basic.thy](proofs/basic/isabelle/Basic.thy)** - Isabelle/HOL foundational proofs
- **[proofs/basic/agda/Basic.agda](proofs/basic/agda/Basic.agda)** - Agda foundational proofs

These files serve as tutorials for researchers learning to use proof assistants and provide CI validation that the formal verification infrastructure is working correctly.

#### Advanced Proof Frameworks for P vs NP
The repository contains four distinct proof frameworks exploring different aspects of the P vs NP problem:

1. **[P = NP Formalization](proofs/p_eq_np/)** (`proofs/p_eq_np/`)
   - Framework for verifying hypothetical proofs that P equals NP
   - Implements four test methods for validating P = NP claims
   - Available in Lean, Rocq, and Isabelle/HOL

2. **[P ≠ NP Formalization](proofs/p_not_equal_np/)** (`proofs/p_not_equal_np/`)
   - Framework for verifying proofs that P does not equal NP
   - See [detailed documentation](proofs/p_not_equal_np/README.md)
   - Includes four mathematically equivalent test methods
   - Available in Lean, Rocq, Isabelle/HOL, and Agda

3. **[P ⊆ NP Formal Proof & Classical Tautology](proofs/p_vs_np_decidable/)** (`proofs/p_vs_np_decidable/`)
   - **Contains the formal proof that P ⊆ NP** ([detailed documentation](proofs/p_vs_np_decidable/README.md))
   - Formalizes that P vs NP has a definite answer in classical logic via law of excluded middle
   - See [detailed documentation](proofs/p_vs_np_decidable/README.md)
   - **Note:** "Decidable" here means the classical tautology that (P=NP) ∨ (P≠NP) holds, NOT algorithmic decidability
   - **The key question:** Is NP ⊆ P provable/unprovable? This determines whether P vs NP is provable/unprovable.
   - Available in Lean, Rocq, Isabelle/HOL, and Agda

4. **[Possible Independence from ZFC](proofs/p_vs_np_undecidable/)** (`proofs/p_vs_np_undecidable/`)
   - Framework for reasoning about potential independence from ZFC (meta-mathematical exploration)
   - See [detailed documentation](proofs/p_vs_np_undecidable/README.md)
   - Explores whether P vs NP could be independent of standard axiom systems
   - Available in Lean, Rocq, Isabelle/HOL, and Agda

#### Historical P vs NP Proof Attempts (`proofs/attempts/`)

The repository includes formal analysis of historical claimed proofs of P vs NP, documenting where each attempt failed:

1. **[Ted Swart (1986/87) - P=NP via Linear Programming](proofs/attempts/ted-swart-1986-87-peqnp/)** (`proofs/attempts/ted-swart-1986-87-peqnp/`)
   - Entry #1 on [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
   - Claimed polynomial-size LP formulations for Hamiltonian cycle
   - Refuted by Yannakakis (STOC 1988): symmetric LP formulations require exponential size
   - See [detailed documentation](proofs/attempts/ted-swart-1986-87-peqnp/README.md)
   - Formalized in Lean, Rocq, and Isabelle/HOL

All proof files are automatically verified by GitHub Actions workflows to ensure correctness. [![Formal Verification Suite](https://github.com/konard/p-vs-np/actions/workflows/verification.yml/badge.svg)](https://github.com/konard/p-vs-np/actions/workflows/verification.yml)

## Key Highlights

### Problem Significance

- **Cryptography:** Many cryptographic schemes rely on *average-case* hardness of specific problems (factoring, discrete logarithm, lattice problems). A constructive proof that **P = NP** with practical algorithms would break most standard public-key cryptosystems, but **P ≠ NP** alone does not guarantee the existence of one-way functions or secure cryptography. **Note on one-way functions (OWFs):** Existence of OWFs would imply P ≠ NP, but P ≠ NP alone does **not** imply OWFs exist—the converse direction is unknown. This is because P ≠ NP only establishes worst-case hardness for some problems, while cryptography requires average-case hardness.
- **Optimization:** Thousands of real-world problems are NP-complete
- **Mathematics:** P = NP would enable automated theorem proving
- **Artificial Intelligence:** Impacts machine learning and automated reasoning

### Current Consensus

- **Most Believed:** P ≠ NP (problems exist that can be verified but not efficiently solved)
- **Major Barriers:**
  - **Relativization** ([Baker, Gill, Solovay, 1975](https://doi.org/10.1137/0204037)): Techniques that work in all oracle worlds cannot resolve P vs NP
  - **Natural Proofs** ([Razborov, Rudich, 1997](https://doi.org/10.1006/jcss.1997.1494)): Under cryptographic assumptions, "natural" techniques cannot prove super-polynomial circuit lower bounds
  - **Algebrization** ([Aaronson, Wigderson, 2008](https://doi.org/10.1145/1536414.1536451)): Extends relativization and arithmetization barriers, showing further limitations
- **Best Known Algorithms:**
  - **2-SAT:** O(n + m) via implication graph + strongly connected components ([Aspvall, Plass, Tarjan, 1979](https://doi.org/10.1016/0020-0190(79)90002-4))
  - **3-SAT:** ~O(1.306973^n) ([PPSZ improvements](https://epubs.siam.org/doi/10.1137/130919876); carries from Unique-3-SAT to general 3-SAT per [Hertli 2014](https://epubs.siam.org/doi/10.1137/130919876))
  - **k-SAT (k≥4):** Base depends on k (PPSZ variants)
  - **General CNF-SAT:** Bounds depend on clause structure
- **Best Lower Bounds:**
  - **General circuits (full binary basis):** ~3.1·n − o(n) gates for explicit functions (Li & Yang, STOC 2022)
    - Prior record: (3 + 1/86)·n − o(n) (Golovnev, Kulikov, Williams et al., FOCS 2016)
  - **Restricted models:** Exponential bounds for monotone circuits, AC⁰, etc.
  - Still far from the super-polynomial bounds needed for P ≠ NP

### Notable Results

- **1971:** Cook proves SAT is NP-complete
- **1972:** Karp identifies 21 NP-complete problems
- **1985:** Razborov proves exponential monotone circuit lower bounds
- **1997:** Razborov-Rudich identify Natural Proofs barrier
- **2011:** Williams proves NEXP ⊄ ACC⁰ ([Williams 2011](https://arxiv.org/abs/1111.1261)) - major non-relativizing result using algorithm-to-lower-bound connection
- **2024:** Continued research with novel approaches (thermodynamic perspectives)
- **2025:** Advances in circuit lower bounds, including:
  - Superpolynomial lower bounds against constant-depth algebraic circuits (Limaye-Srinivasan-Tavenas, J. ACM 2025)
  - Quantum circuit lower bounds in the magic hierarchy, showing state preparation limits (Parham 2025, [arXiv:2504.19966](https://arxiv.org/abs/2504.19966))

## Getting Started

### For Researchers

1. Read [P_VS_NP_TASK_DESCRIPTION.md](P_VS_NP_TASK_DESCRIPTION.md) for comprehensive background
2. Study [TOOLS_AND_METHODOLOGIES.md](TOOLS_AND_METHODOLOGIES.md) to understand available techniques
3. Follow [DETAILED_SOLUTION_PLAN.md](DETAILED_SOLUTION_PLAN.md) for structured research approach

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

This is a research repository. Contributions welcome:
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

### Core Documentation
- [README.md](README.md) - This file (repository overview)
- [P_VS_NP_TASK_DESCRIPTION.md](P_VS_NP_TASK_DESCRIPTION.md) - Comprehensive problem description
- [TOOLS_AND_METHODOLOGIES.md](TOOLS_AND_METHODOLOGIES.md) - Tools, techniques, and resources
- [DETAILED_SOLUTION_PLAN.md](DETAILED_SOLUTION_PLAN.md) - Multi-phase research plan
- [SOLUTION_STRATEGIES.md](SOLUTION_STRATEGIES.md) - Catalog of 17 solution strategies for formal testing
- [SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md](SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md) - Solution strategies for decidability testing
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Catalog of solution strategies for P ≠ NP
- [P_VS_NP_INDEPENDENCE_STRATEGIES.md](P_VS_NP_INDEPENDENCE_STRATEGIES.md) - Solution strategies for testing independence

### Formal Verification Documentation
- [Basic Proofs](proofs/basic/) - Foundational proofs in multiple proof assistants
- [P = NP Framework](proofs/p_eq_np/) - Framework for verifying P = NP proofs
- [P ≠ NP Framework](proofs/p_not_equal_np/README.md) - Framework for verifying P ≠ NP proofs
- [Classical Tautology](proofs/p_vs_np_decidable/README.md) - Formalization that (P=NP) ∨ (P≠NP) holds in classical logic
- [Possible Independence from ZFC](proofs/p_vs_np_undecidable/README.md) - Framework for meta-mathematical independence reasoning
- [Historical Proof Attempts](proofs/attempts/) - Formal analysis of failed P vs NP attempts
  - [Ted Swart (1986/87)](proofs/attempts/ted-swart-1986-87-peqnp/README.md) - P=NP via linear programming (refuted by Yannakakis)

All documents are interlinked - you can navigate between them using hyperlinks within each file.

---

**Important Notes:**
- This repository provides educational and research materials for studying complexity theory and the P vs NP problem.
- The goal is to advance understanding, develop research skills, and contribute to complexity theory—not to claim a solution to P vs NP on a fixed timeline.
- Resolving P vs NP likely requires fundamentally new mathematical insights beyond currently known techniques.
- Any claimed proof must address known barriers (relativization, natural proofs, algebrization) and undergo rigorous peer review.
