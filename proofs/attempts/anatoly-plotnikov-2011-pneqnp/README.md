# Anatoly Plotnikov (2011) - P≠NP Attempt

[← Back to Attempts](../) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

**Attempt ID**: 77 (from Woeginger's list)
**Author**: Anatoly D. Plotnikov
**Year**: 2011
**Claim**: P ≠ NP
**Paper Title**: "A Proof that P is not equal to NP"
**Status**: Refuted (contains fundamental logical errors)

## Summary

In 2011, Ukrainian mathematician Anatoly D. Plotnikov — who had previously made two attempts to prove P=NP (entries #2 and #39 on Woeginger's list) — reversed course and claimed to prove P≠NP. His argument attempts to show that no polynomial-time algorithm can solve the 3-Colorability problem (which is NP-complete), thereby establishing P≠NP.

The proof attempts to use a diagonalization-style argument combined with an analysis of graph colorability, but contains critical logical flaws that invalidate the conclusion.

## Main Argument/Approach

### The Problem Addressed: 3-Colorability

The **3-Colorability problem** (3-COL) asks: Given an undirected graph G = (V, E), can its vertices be colored with at most 3 colors such that no two adjacent vertices share the same color?

**Key Facts**:
- 3-COL is NP-complete (proved by Karp in 1972)
- The decision version ("Is G 3-colorable?") is NP-complete
- Any polynomial-time algorithm for 3-COL would establish P=NP
- The complement: if no polynomial-time algorithm exists for 3-COL, it supports P≠NP

### Plotnikov's Proof Strategy

Plotnikov's argument proceeds roughly as follows:

1. **Assume for contradiction**: Suppose there exists a polynomial-time algorithm A that decides 3-Colorability.

2. **Construct a special graph family**: Build a family of graphs G_n with specific structural properties related to the algorithm A's operation.

3. **Diagonal argument**: Using a self-referential construction reminiscent of diagonalization, construct a graph G* such that A(G*) gives the wrong answer — either claiming G* is 3-colorable when it is not, or vice versa.

4. **Contradiction**: The contradictory answer shows A cannot be correct, hence no polynomial-time algorithm for 3-COL exists.

5. **Conclusion**: Since 3-COL is NP-complete and cannot be solved in polynomial time, P≠NP.

### Key Technical Claims

The paper's central technical claims are:

- The diagonal construction produces a well-defined graph G* for any purported polynomial-time algorithm A
- A(G*) must give an incorrect answer by the construction
- This refutes the assumption that A exists
- The argument applies uniformly to all polynomial-time algorithms

## The Error in the Proof

Plotnikov's proof contains several fundamental logical flaws:

### Critical Flaw 1: Invalid Diagonalization

**Location**: Core construction of the diagonal graph G*

**The Error**: Plotnikov's diagonalization argument does not properly account for the fact that the algorithm A and the graph G* are intertwined — the construction of G* depends on A, but A's correctness on G* is what is being tested.

**Why This Matters**: Valid diagonalization arguments (such as those used to prove the undecidability of the Halting Problem) work because:
- The diagonalized object (the problematic input) is well-defined independently of the algorithm
- The algorithm cannot "cheat" by detecting it is being diagonalized

In P vs NP, this approach faces an insurmountable obstacle: **P and NP are complexity classes defined over all inputs**, not individual problem instances. A purported polynomial-time algorithm A might handle the diagonal graph G* just fine, with the flaw being in Plotnikov's assumption that it cannot.

**Specifically**: The construction "A accepts G* iff G* is not 3-colorable" is circular — determining whether G* is 3-colorable is the very problem being studied, and Plotnikov assumes the answer without proving it.

### Critical Flaw 2: Conflation of Semantic and Syntactic Properties

**Location**: Throughout the proof

**The Error**: The proof treats the computational behavior of the algorithm A on G* as if it can be determined by syntactic inspection of the graph structure, without actually running A.

**Why This Matters**: Whether a polynomial-time algorithm A accepts or rejects a given graph depends on A's complete computation, which may involve complex intermediate steps not captured by simple graph properties.

### Critical Flaw 3: Failure to Account for Non-Uniform Computation

**Location**: The generalization step

**The Error**: Even if the argument worked for one specific algorithm A, it would not automatically generalize to show that NO polynomial-time algorithm exists. The proof does not properly quantify over all possible polynomial-time algorithms.

**Why This Matters**: Proving P≠NP requires showing that no polynomial-time algorithm — not just specific ones — can solve 3-COL. A valid proof must handle all possible algorithms, including ones that use techniques not anticipated by the proof author.

### Critical Flaw 4: Circular Reasoning

**Location**: The diagonal construction

**The Error**: The proof assumes knowledge of whether G* is 3-colorable in order to construct the contradiction. But this is exactly what the algorithm A is supposed to decide — so the proof assumes the answer to prove the answer is wrong.

**More precisely**: The construction says "A accepts G* iff G* is not 3-colorable." To verify this leads to a contradiction, one must know whether A accepts G*. But this requires running A on G*, which requires knowing A's output, which requires... the same question.

## Why This Problem Is Hard

Proving P≠NP is believed to be one of the hardest problems in mathematics:

- **Baker-Gill-Solovay theorem** (1975): Diagonalization-based techniques (relativization) cannot separate P from NP in general, because there exist oracles relative to which P=NP and oracles relative to which P≠NP.
- **Natural proofs barrier** (Razborov-Rudich, 1994): A large class of circuit lower bound proof techniques cannot prove super-polynomial lower bounds if strong pseudorandom generators exist.
- **Algebrization barrier** (Aaronson-Wigderson, 2009): Algebraic extensions of relativization also cannot resolve P vs NP.
- **Decades of failed attempts**: Despite the efforts of the best mathematicians worldwide, no valid proof has been found.

Plotnikov's approach suffers from the relativization barrier — diagonalization-style arguments cannot separate P from NP.

## Formalization Strategy

The formalization documents Plotnikov's claimed argument and identifies precisely where it fails.

### proof/ directory
- Formalizes Plotnikov's argument as faithfully as possible
- Uses axioms for unproven claims
- Marks where the argument breaks down with detailed comments

### refutation/ directory
- Formally states why each flaw is fatal
- References the relativization barrier
- Demonstrates the circular reasoning with formal logic

## Status

- [x] README.md
- [x] ORIGINAL.md (reconstruction from known sources)
- [ ] ORIGINAL.pdf (paper not publicly available; see ORIGINAL.md)
- [x] proof/README.md
- [x] proof/lean/PlotnikovPNEQNP.lean
- [x] proof/rocq/PlotnikovPNEQNP.v
- [x] refutation/README.md
- [x] refutation/lean/PlotnikovRefutation.lean
- [x] refutation/rocq/PlotnikovRefutation.v

Note: ORIGINAL.pdf is not available because the paper was never published on arXiv
or other major public repositories. The argument is reconstructed in ORIGINAL.md.

## Key Lessons

1. **Diagonalization cannot separate P from NP**: The Baker-Gill-Solovay theorem shows this, and Plotnikov's attempt succumbs to this barrier.
2. **Circular reasoning is common in P vs NP attempts**: Assuming what you are trying to prove is a recurring failure mode.
3. **Uniform vs non-uniform arguments**: Proving a specific algorithm fails does not prove all algorithms fail.
4. **The reversibility of error**: Plotnikov previously claimed P=NP (entries #2 and #39), then claimed P≠NP — the ease of switching sides reveals neither claim had a rigorous foundation.
5. **Self-reference traps**: Diagonalization arguments that make an algorithm reason about its own behavior on a constructed input often contain hidden circularities.

## References

1. **Plotnikov's Claimed Proof**: Plotnikov, A. D. (2011). "A Proof that P is not equal to NP." Entry #77 on Woeginger's list.
   https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

2. **Plotnikov's Earlier Attempts**:
   - Entry #2 (1996): `../author2-1996-peqnp/`
   - Entry #39 (2007): `../anatoly-plotnikov-2007-peqnp/`

3. **Baker-Gill-Solovay Theorem**: Baker, T., Gill, J., and Solovay, R. (1975). "Relativizations of the P=?NP Question." *SIAM Journal on Computing*, 4(4), pp. 431–442.

4. **Natural Proofs Barrier**: Razborov, A. A. and Rudich, S. (1994). "Natural Proofs." *Proceedings of the 26th ACM Symposium on Theory of Computing (STOC)*, pp. 204–213.

5. **Algebrization Barrier**: Aaronson, S. and Wigderson, A. (2009). "Algebrization: A New Barrier in Complexity Theory." *ACM Transactions on Computation Theory*, 1(1).

6. **3-Colorability NP-completeness**: Karp, R. M. (1972). "Reducibility Among Combinatorial Problems." In R. E. Miller and J. W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press, pp. 85–103.

7. **Woeginger's List**: Entry #77 on Gerhard Woeginger's "The P-versus-NP page"
   https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Directory Structure

```
anatoly-plotnikov-2011-pneqnp/
├── README.md (this file)
├── ORIGINAL.md
├── proof/
│   ├── README.md
│   ├── lean/
│   │   └── PlotnikovPNEQNP.lean
│   └── rocq/
│       └── PlotnikovPNEQNP.v
└── refutation/
    ├── README.md
    ├── lean/
    │   └── PlotnikovRefutation.lean
    └── rocq/
        └── PlotnikovRefutation.v
```

---

*This formalization is part of the [P vs NP formal verification project](../../..) - Issue #478*

[← Back to Attempts](../) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
