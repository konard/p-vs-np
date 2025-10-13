# Tools and Methodologies for Approaching the P vs NP Problem

## Overview

This document catalogs the theoretical tools, mathematical methodologies, computational techniques, and resources available for studying and potentially solving the P vs NP problem. It serves as a comprehensive guide for researchers approaching this fundamental question in computational complexity theory.

---

## 1. Theoretical Foundations

### 1.1 Computational Models

**Turing Machines**
- **Purpose:** Formal model of computation; standard for defining P and NP
- **Variants:**
  - Single-tape deterministic Turing machine (DTM)
  - Multi-tape Turing machine
  - Nondeterministic Turing machine (NTM)
  - Oracle Turing machine
  - Alternating Turing machine
- **Tools for Analysis:**
  - Time complexity T(n) = worst-case number of steps
  - Space complexity S(n) = worst-case cells used
  - Configuration graphs
  - Computation tableaus
- **Key Resources:**
  - Sipser's "Introduction to the Theory of Computation"
  - Papadimitriou's "Computational Complexity"

**Boolean Circuits**
- **Purpose:** Non-uniform model; essential for lower bound techniques
- **Components:**
  - Gates: AND, OR, NOT, NAND, NOR
  - Unbounded fan-in variants
  - Special gates: MOD, MAJORITY, THRESHOLD
- **Measures:**
  - Size: Number of gates
  - Depth: Longest path from input to output
  - Width: Maximum number of gates at any level
- **Circuit Classes:**
  - NC: Polylog depth, polynomial size
  - AC^0: Constant depth, unbounded fan-in AND/OR
  - TC^0: AC^0 plus MAJORITY gates
  - ACC^0: AC^0 plus MOD gates
- **Tools:**
  - Circuit simulators
  - Circuit complexity libraries

**Boolean Functions**
- **Representations:**
  - Truth tables
  - DNF/CNF (disjunctive/conjunctive normal forms)
  - Binary decision diagrams (BDDs)
  - Polynomials over finite fields
- **Complexity Measures:**
  - Circuit complexity
  - Formula size
  - Decision tree complexity
  - Communication complexity
  - Polynomial degree

### 1.2 Complexity Classes

**Resource-Bounded Classes**
- **Time-Bounded:**
  - DTIME(f(n)): Deterministic time f(n)
  - NTIME(f(n)): Nondeterministic time f(n)
  - P = ⋃ₖ DTIME(n^k)
  - NP = ⋃ₖ NTIME(n^k)
  - EXP, NEXP, 2-EXP
- **Space-Bounded:**
  - DSPACE(f(n)), NSPACE(f(n))
  - L (log-space), NL, PSPACE
- **Circuit-Bounded:**
  - P/poly: Polynomial-size circuits
  - LINEAR-SIZE: O(n)-size circuits

**Probabilistic Classes**
- **BPP:** Bounded-error probabilistic polynomial time
- **RP, coRP:** One-sided error
- **ZPP:** Zero-error probabilistic polynomial time
- **PP:** Unbounded-error probabilistic polynomial time

**Quantum Classes**
- **BQP:** Bounded-error quantum polynomial time
- **QMA:** Quantum Merlin-Arthur

**Interactive Classes**
- **IP:** Interactive polynomial time
- **AM, MA:** Arthur-Merlin protocols
- **PCP:** Probabilistically checkable proofs

**Hierarchy Classes**
- **Polynomial Hierarchy (PH):**
  - Σₙᴾ, Πₙᴾ, Δₙᴾ for n ≥ 0
  - Σ₀ᴾ = Π₀ᴾ = P
  - Σ₁ᴾ = NP, Π₁ᴾ = coNP
- **Boolean Hierarchy**
- **Counting Hierarchy**

**Tools for Class Analysis:**
- Inclusion diagrams
- Closure properties
- Complete problems
- Hierarchy theorems

---

## 2. Mathematical Tools

### 2.1 Combinatorics and Discrete Mathematics

**Graph Theory**
- **Applications:**
  - Modeling NP-complete problems (clique, coloring, Hamiltonian cycle)
  - Expander graphs for pseudorandomness
  - Graph minors (Robertson-Seymour)
- **Tools:**
  - Graph algorithms libraries (NetworkX, igraph)
  - Visualization tools (Graphviz, Gephi)

**Combinatorial Optimization**
- **Techniques:**
  - Matching theory
  - Network flows
  - Matroids
  - Linear programming
  - Integer programming
- **Software:**
  - CPLEX, Gurobi (commercial)
  - GLPK, OR-Tools (open-source)

**Ramsey Theory and Extremal Combinatorics**
- **Relevance:** Lower bounds, counting arguments
- **Techniques:**
  - Probabilistic method
  - Regularity lemmas
  - Turán-type theorems

### 2.2 Algebra

**Polynomial Methods**
- **Applications:**
  - Circuit lower bounds (Razborov-Smolensky)
  - IP = PSPACE proof
  - Algebraic complexity theory
- **Techniques:**
  - Polynomials over finite fields (F₂, Fₚ)
  - Polynomial interpolation
  - Degree bounds
  - Multilinear polynomials
- **Tools:**
  - Computer algebra systems (Mathematica, Sage, Macaulay2)

**Linear Algebra**
- **Applications:**
  - Communication complexity
  - Matrix rank methods
  - Span programs
- **Techniques:**
  - Rank arguments
  - Eigenvalues and spectral methods
  - Tensor decompositions

**Group Theory and Representation Theory**
- **Applications:**
  - Geometric complexity theory
  - Symmetries in computation
- **Advanced Topics:**
  - Representation theory of symmetric groups
  - Algebraic geometry connections

### 2.3 Logic and Proof Theory

**Propositional Logic**
- **Applications:**
  - SAT problem formulation
  - Proof complexity
- **Proof Systems:**
  - Resolution
  - Cutting planes
  - Frege systems
  - Extended Frege
- **Tools:**
  - SAT solvers (MiniSat, CryptoMiniSat, Z3)
  - Proof checkers

**First-Order Logic**
- **Applications:**
  - Descriptive complexity
  - Finite model theory
- **Key Results:**
  - Fagin's theorem: NP = existential second-order logic
  - Immerman-Szelepcsényi: NL = coNL

**Model Theory**
- **Applications:**
  - 0-1 laws
  - Logical characterizations of complexity classes

### 2.4 Probability and Randomness

**Probabilistic Method**
- **Applications:**
  - Existence proofs
  - Randomized algorithms
  - Circuit lower bounds
- **Techniques:**
  - First moment method
  - Second moment method
  - Lovász Local Lemma
  - Concentration inequalities (Chernoff, Azuma)

**Pseudorandomness**
- **Concepts:**
  - Pseudorandom generators (PRGs)
  - Expander graphs
  - Extractors
  - Derandomization
- **Key Results:**
  - Impagliazzo-Wigderson: hard functions imply PRGs
  - Nisan-Wigderson generator
- **Tools:**
  - Random number testing suites
  - Pseudorandom generator implementations

**Information Theory**
- **Applications:**
  - Communication complexity
  - Entropy bounds
  - Kolmogorov complexity
- **Measures:**
  - Shannon entropy
  - Mutual information
  - Kolmogorov complexity
- **Tools:**
  - Entropy calculation libraries

### 2.5 Analysis and Topology

**Real Analysis**
- **Applications:**
  - Approximation algorithms
  - Smoothed analysis
- **Techniques:**
  - Fourier analysis
  - Harmonic analysis
  - Approximation theory

**Algebraic Geometry**
- **Applications:**
  - Geometric complexity theory (GCT)
  - Valiant's algebraic complexity classes
- **Concepts:**
  - Varieties and ideals
  - Orbit closures
  - Representation-theoretic obstructions
- **Tools:**
  - Macaulay2
  - Singular
  - CoCoA

---

## 3. Proof Techniques

### 3.1 Classical Techniques

**Diagonalization**
- **Method:** Construct problem that differs from all polynomial-time algorithms
- **Applications:**
  - Time hierarchy theorem
  - Space hierarchy theorem
  - P ⊊ EXP
- **Limitation:** Relativization barrier for P vs NP
- **Tools:**
  - Enumeration of Turing machines
  - Universal Turing machine constructions

**Simulation and Reduction**
- **Types:**
  - Many-one reductions (≤ₘ)
  - Turing reductions (≤T)
  - Polynomial-time reductions (≤p)
  - Log-space reductions (≤L)
- **Applications:**
  - Proving NP-completeness
  - Class inclusions
- **Technique:** Show L₁ ≤p L₂ and L₂ ∈ P implies L₁ ∈ P

**Padding Arguments**
- **Method:** Scale problem instances to relate classes at different time bounds
- **Applications:**
  - Relating P vs NP to other separations
  - Downward separations

### 3.2 Circuit Lower Bounds

**Monotone Circuit Lower Bounds**
- **Method:** Analyze circuits without NOT gates
- **Key Result:** Razborov (1985) - monotone circuit for CLIQUE requires exponential size
- **Technique:** Approximation method
- **Limitation:** Doesn't apply to general circuits

**Constant-Depth Circuit Lower Bounds**
- **Ajtai (1983), Furst-Saxe-Sipser (1984):**
  - PARITY not in AC^0
  - Method: Switching lemma, random restrictions
- **Håstad (1987):**
  - Optimal AC^0 lower bounds
  - Refined switching lemma
- **Razborov-Smolensky (1987):**
  - ACC^0 lower bounds for MOD functions
  - Method: Polynomial approximation

**Communication Complexity Lower Bounds**
- **Method:** Study communication required for distributed computation
- **Applications:**
  - Circuit depth lower bounds
  - Streaming algorithms
  - Data structure lower bounds
- **Techniques:**
  - Fooling sets
  - Rank arguments
  - Discrepancy method
  - Information complexity

**Algebraic Methods**
- **Polynomial Degree Bounds:**
  - Lower bound degree of polynomial representing function
- **Arithmetic Circuit Lower Bounds:**
  - VP vs VNP (Valiant's classes)
  - Permanent vs determinant

### 3.3 Algorithm Design Implies Lower Bounds

**Williams' Technique (2010)**
- **Insight:** Better algorithms for circuit satisfiability imply circuit lower bounds
- **Result:** NEXP ⊄ ACC^0
- **Method:**
  1. Design fast satisfiability algorithm for circuit class C
  2. Use algorithm in diagonalization
  3. Conclude NEXP or NEXP/poly not in C
- **Significance:** First major non-relativizing separation in decades

**Tools for Implementation:**
- Algorithm analysis
- Satisfiability algorithms
- Derandomization techniques

### 3.4 Natural Proofs and Barriers

**Natural Proofs Framework (Razborov-Rudich, 1997)**
- **Properties of Natural Proofs:**
  1. **Constructivity:** Can efficiently recognize "hard" functions
  2. **Largeness:** Many functions satisfy the property
  3. **Usefulness:** Property implies super-polynomial lower bounds
- **Barrier:** If strong PRGs exist, natural proofs can't prove P/poly lower bounds
- **Implication:** Need non-natural techniques

**Overcoming Barriers:**
- Non-relativizing techniques (arithmetization, algebraic methods)
- Non-naturalizing techniques (specific structure, non-uniformity gaps)
- Algorithm-to-lower-bound connections (Williams' approach)

### 3.5 Indirect and Structural Approaches

**Polynomial Hierarchy Collapse**
- **Strategy:** Show P = NP implies unexpected consequences
- **Example:** If P = NP, then PH collapses to P

**Average-Case vs Worst-Case**
- **Approach:** Study average-case complexity
- **Tools:**
  - Levin's average-case completeness
  - Hardness amplification
  - Worst-case to average-case reductions

**Cryptographic Approaches**
- **Insight:** Cryptographic hardness assumptions related to P vs NP
- **Tools:**
  - One-way functions
  - Pseudorandom generators
  - Hardness assumptions

---

## 4. Computational Tools

### 4.1 SAT Solvers

**Modern CDCL Solvers**
- **Examples:** MiniSat, CryptoMiniSat, Glucose, Lingeling
- **Features:**
  - Conflict-driven clause learning (CDCL)
  - Watched literals
  - Restart strategies
  - Clause deletion
- **Use Cases:**
  - Solving practical SAT instances
  - Understanding why real instances easier than worst-case
  - Benchmarking

**SMT Solvers**
- **Examples:** Z3, CVC5, Yices
- **Capabilities:**
  - Satisfiability modulo theories
  - Integration of SAT with background theories
  - Verification applications

**Portfolio Solvers**
- **Examples:** SATzilla, ppfolio
- **Method:** Machine learning to select best solver for instance

### 4.2 Constraint Satisfaction and Optimization

**CP Solvers**
- **Examples:** Gecode, OR-Tools, MiniZinc
- **Applications:**
  - Constraint satisfaction problems
  - Scheduling
  - Planning

**MIP Solvers**
- **Examples:** CPLEX, Gurobi, SCIP
- **Capabilities:**
  - Mixed integer programming
  - Branch and bound
  - Cutting planes
  - Heuristics

### 4.3 Proof Assistants and Verification

**Interactive Theorem Provers**
- **Examples:** Coq, Isabelle/HOL, Lean
- **Applications:**
  - Formalizing complexity theory
  - Verified proofs
  - Checking reasoning
- **Notable Proofs:**
  - Four-color theorem (Coq)
  - Kepler conjecture (Isabelle)

**Automated Theorem Provers**
- **Examples:** E, Vampire, SPASS
- **Applications:**
  - Automated proof search
  - Proof complexity studies

### 4.4 Symbolic Computation

**Computer Algebra Systems**
- **Examples:**
  - Mathematica (commercial)
  - Maple (commercial)
  - Sage (open-source)
  - Maxima (open-source)
- **Capabilities:**
  - Symbolic manipulation
  - Polynomial computation
  - Algebraic geometry

**Specialized Systems**
- **Macaulay2:** Algebraic geometry, commutative algebra
- **Singular:** Polynomial computations
- **GAP:** Group theory

### 4.5 Simulation and Experimentation

**Turing Machine Simulators**
- **Purpose:** Understand computational models
- **Examples:** Custom implementations, educational tools

**Circuit Simulators**
- **Purpose:** Design and analyze Boolean circuits
- **Tools:**
  - ABC (Berkeley)
  - Custom circuit libraries

**Algorithm Visualization**
- **Tools:** Algorithm animation systems
- **Purpose:** Understanding algorithm behavior

### 4.6 Libraries and Frameworks

**Complexity Theory Libraries**
- **Examples:**
  - Complexity Zoo (database of classes)
  - PyCryptodome (cryptographic primitives)
  - Custom research code

**Graph Libraries**
- **Examples:**
  - NetworkX (Python)
  - igraph (R, Python, C)
  - Boost Graph Library (C++)
- **Purpose:** Implementing graph algorithms

**Combinatorial Libraries**
- **Sage:** Comprehensive mathematical software
- **Purpose:** Combinatorics, graph theory, algebra

---

## 5. Research Methodologies

### 5.1 Theoretical Research

**Literature Review**
- **Key Venues:**
  - Conferences: STOC, FOCS, CCC, ICALP, SODA
  - Journals: JACM, SICOMP, Computational Complexity, Theory of Computing
- **Resources:**
  - ACM Digital Library
  - IEEE Xplore
  - arXiv.org (cs.CC section)
  - ECCC (Electronic Colloquium on Computational Complexity)

**Collaboration and Communication**
- **Methods:**
  - Research seminars
  - Workshops and conferences
  - Online forums (cstheory.stackexchange.com)
  - Collaboration platforms

**Proof Development**
- **Process:**
  1. Intuition and conjectures
  2. Special cases
  3. Formal proof sketch
  4. Rigorous proof
  5. Verification
  6. Peer review
- **Tools:**
  - LaTeX for writeup
  - Proof assistants for verification
  - Collaboration tools (Overleaf, Git)

### 5.2 Computational Experiments

**Empirical Analysis of Algorithms**
- **Method:**
  - Implement algorithms
  - Test on benchmarks
  - Analyze running time
- **Purpose:**
  - Understand practical behavior
  - Validate theoretical predictions
  - Generate conjectures

**Instance Generation**
- **Types:**
  - Random instances
  - Structured instances
  - Hard instances
  - Phase transitions
- **Tools:**
  - Instance generators
  - SATLIB benchmark library

**Heuristic Evaluation**
- **Method:**
  - Design heuristics for NP-complete problems
  - Compare to optimal or best-known solutions
  - Statistical analysis

### 5.3 Interdisciplinary Approaches

**Connections to Physics**
- **Statistical mechanics:**
  - Phase transitions in satisfiability
  - Spin glass models
  - Entropy methods (2024 thermodynamic approach)
- **Quantum computation:**
  - Quantum complexity classes
  - Quantum algorithms

**Connections to Cryptography**
- **One-way functions:**
  - Existence related to P vs NP
  - Cryptographic hardness assumptions
- **Applications:**
  - RSA, DES security
  - Blockchain and consensus

**Connections to Optimization**
- **Operations research:**
  - Practical solving of NP-complete problems
  - Approximation algorithms
  - Heuristics
- **Machine learning:**
  - Computational learning theory
  - PAC learning
  - VC dimension

**Connections to Philosophy**
- **Computational epistemology**
- **Foundations of mathematics**
- **Independence from axioms**

---

## 6. Specific Research Programs

### 6.1 Geometric Complexity Theory (GCT)

**Goals:**
- Prove P ≠ NP or VP ≠ VNP via algebraic geometry
- Use representation theory and orbit closures

**Key Concepts:**
- **Orbit closures:** Geometric objects representing complexity
- **Representation-theoretic obstructions:** Barriers to simulation
- **Mulmuley-Sohoni program:** Long-term research agenda

**Tools:**
- Algebraic geometry (Macaulay2, Singular)
- Representation theory (GAP, Sage)
- Group theory

**Status:**
- Long-term program
- Partial results on representation-theoretic barriers
- Full resolution not yet achieved

**Resources:**
- Mulmuley's papers and lectures
- GCT workshop proceedings

### 6.2 Proof Complexity

**Goals:**
- Understand propositional proof systems
- Connect to NP vs coNP

**Key Result:**
- If NP ≠ coNP, no proof system has polynomial-size proofs for all tautologies

**Research Areas:**
- Lower bounds for resolution
- Frege system analysis
- Extended Frege systems
- Algebraic proof systems (IPS)

**Tools:**
- Proof complexity libraries
- Automated proof generation

**Resources:**
- Krajíček's "Proof Complexity"
- Recent papers in CCC, STOC, FOCS

### 6.3 Derandomization

**Goal:**
- Prove BPP = P
- Eliminate randomness from algorithms

**Approaches:**
- **Pseudorandom generators:**
  - Construct PRGs from hard functions
  - Impagliazzo-Wigderson framework
- **Hardness vs randomness:**
  - Hard functions imply derandomization

**Connection to P vs NP:**
- If E requires exponential circuits, then BPP = P
- If E has small circuits, then P ≠ NP (Kabanets)

**Tools:**
- PRG implementations
- Hardness amplification techniques

### 6.4 Fine-Grained Complexity

**Goal:**
- Understand relationships within P
- Classify problems by best possible running time

**Key Hypotheses:**
- **Strong Exponential Time Hypothesis (SETH):** SAT requires 2^n time
- **3SUM hypothesis**
- **APSP hypothesis**

**Method:**
- Conditional lower bounds based on conjectures
- Fine-grained reductions

**Relevance:**
- Understanding structure within P
- Practical algorithm design

---

## 7. Experimental and Empirical Tools

### 7.1 Benchmarking Suites

**SAT Benchmarks**
- **SAT Competition:** Annual competition, curated instances
- **SATLIB:** Classic benchmark library
- **Industrial instances:** From verification, planning, etc.

**Optimization Benchmarks**
- **MIPLIB:** Mixed integer programming instances
- **TSPLIB:** Traveling salesman problem instances
- **Graph benchmark suites**

### 7.2 Performance Analysis

**Profiling Tools**
- **Purpose:** Understand algorithm bottlenecks
- **Tools:** gprof, Valgrind, Intel VTune

**Visualization**
- **Purpose:** Understand algorithm behavior
- **Tools:** Custom visualizations, animation

### 7.3 Statistical Analysis

**Hypothesis Testing**
- **Purpose:** Validate experimental results
- **Methods:** t-tests, ANOVA, non-parametric tests

**Regression Analysis**
- **Purpose:** Understand scaling behavior
- **Tools:** R, Python (scipy.stats, scikit-learn)

---

## 8. Educational Resources

### 8.1 Textbooks

**Foundational:**
- Sipser, "Introduction to the Theory of Computation"
- Papadimitriou, "Computational Complexity"
- Arora-Barak, "Computational Complexity: A Modern Approach"

**Advanced:**
- Goldreich, "Computational Complexity: A Conceptual Perspective"
- Krajíček, "Proof Complexity"
- Jukna, "Boolean Function Complexity"

**Related Areas:**
- Cormen et al., "Introduction to Algorithms"
- Garey-Johnson, "Computers and Intractability"

### 8.2 Online Resources

**Courses:**
- MIT OpenCourseWare: 6.045, 6.840
- Stanford: CS254, CS254B
- Princeton: COS 522, COS 433
- Berkeley: CS172, CS278

**Lecture Notes:**
- Scott Aaronson's lecture notes
- Luca Trevisan's blog and notes
- Lance Fortnow and Bill Gasarch's blog

**Databases:**
- Complexity Zoo: Comprehensive class database
- ECCC: Electronic Colloquium on Computational Complexity

### 8.3 Community

**Forums:**
- cstheory.stackexchange.com
- Theoretical Computer Science on Reddit
- Research blogs

**Conferences:**
- **STOC:** Symposium on Theory of Computing
- **FOCS:** Foundations of Computer Science
- **CCC:** Computational Complexity Conference
- **ICALP:** International Colloquium on Automata, Languages and Programming
- **SODA:** Symposium on Discrete Algorithms

---

## 9. Practical Advice for Research

### 9.1 Getting Started

**Build Foundation:**
1. Study computational models (Turing machines, circuits)
2. Learn complexity classes and their relationships
3. Understand NP-completeness thoroughly
4. Study major results and proof techniques

**Study Barriers:**
- Understand why P vs NP is hard
- Learn relativization, natural proofs, algebrization
- Study what techniques are blocked

**Focus Areas:**
- Choose specific approach (lower bounds, algorithms, structural, etc.)
- Become expert in specialized area
- Build from existing work

### 9.2 Research Strategy

**Start Small:**
- Study restricted models first
- Work on related but simpler problems
- Build intuition gradually

**Collaborate:**
- Complexity theory is collaborative
- Attend workshops and conferences
- Engage with community

**Be Creative:**
- Novel approaches may be needed
- Interdisciplinary connections valuable
- Don't be afraid to try new techniques

**Be Skeptical:**
- Many false proofs have been proposed
- Verify carefully
- Peer review essential

### 9.3 Common Pitfalls

**Mistakes to Avoid:**
1. **Relativization:** Using techniques that relativize
2. **Non-uniformity:** Confusing uniform and non-uniform models
3. **Average vs worst-case:** Solving average case doesn't imply P = NP
4. **Special cases:** Solving 3-SAT for specific formulas isn't enough
5. **Approximation:** Approximation algorithms don't resolve P vs NP

**Red Flags:**
- Proof seems too simple
- Doesn't account for known barriers
- Uses diagonalization alone
- Claims to resolve P vs NP in few pages

---

## 10. Future Directions

### 10.1 Emerging Approaches

**Thermodynamic Methods (2024):**
- Information theory and entropy
- Statistical mechanics connections
- Energy landscapes of problems

**Meta-Complexity:**
- Complexity of problems about complexity
- Minimum circuit size problem
- MCSP and its role

**Algorithmic Improvements:**
- Better SAT algorithms imply lower bounds (Williams' approach)
- Understanding limits of algorithms

### 10.2 Open Problems Beyond P vs NP

**Related Major Questions:**
- NP vs coNP
- NP vs PSPACE
- L vs NL
- P vs BPP (derandomization)
- Polynomial hierarchy structure

**Circuit Complexity:**
- Super-linear lower bounds for general circuits
- Understanding P/poly vs NP

**Cryptographic Foundations:**
- One-way functions existence
- Connection to P vs NP

---

## Conclusion

The tools and methodologies for approaching P vs NP span mathematics, computer science, logic, and physics. Success likely requires:
1. Deep understanding of existing techniques
2. Recognition of fundamental barriers
3. Novel mathematical insights
4. Possibly interdisciplinary connections
5. Persistence and creativity

The problem has resisted 50+ years of attack by brilliant researchers, suggesting that either fundamentally new techniques are needed, or the problem may be extraordinarily difficult (or even independent of standard axioms).

**Recommended Starting Point:**
- Study Arora-Barak textbook thoroughly
- Understand NP-completeness and reductions deeply
- Learn circuit complexity and lower bound techniques
- Study known barriers (relativization, natural proofs)
- Identify specific research direction
- Engage with research community

**Key Insight:** Progress on P vs NP may come from solving related problems, developing new techniques, or understanding why existing techniques fail. Even partial progress is valuable to the field.
