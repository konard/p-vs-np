# Forward Proof Attempts

This folder contains formalizations that follow the original proof ideas from Delacorte and Czerwinski's papers, showing exactly where and how they fail.

## Paper 1: Delacorte's PSPACE-Completeness Claim

**Original Argument** (from delacorte-2007.pdf):

1. Regular expression equivalence is PSPACE-complete (Meyer & Stockmeyer, 1972)
2. Regular expressions, right-linear grammars, and finite automata are equivalent
3. Graph isomorphism and finite automaton isomorphism are polynomially equivalent (Booth, 1978)
4. Therefore, graph isomorphism is PSPACE-complete

**The Critical Error**:

The argument conflates two different problems:
- **Equivalence**: Do two automata accept the same language? (PSPACE-complete)
- **Isomorphism**: Do two automata have the same structure? (polynomial-time equivalent to GI)

These are fundamentally different problems. The PSPACE-completeness applies to language equivalence, not structural isomorphism.

**Formalization Goal**:

The Lean and Rocq formalizations in this folder demonstrate:
1. How to properly define both "equivalence" and "isomorphism" for finite automata
2. That Booth's result connects GI to automaton **isomorphism**, not equivalence
3. That the claimed reduction chain breaks at the conflation point
4. Why this error invalidates the PSPACE-completeness claim

## Paper 2: Czerwinski's Polynomial-Time Algorithm

**Original Argument** (from the 2007 version, before 2022 retraction):

1. Two graphs are isomorphic iff there exists a permutation matrix P such that A' = P × A × P^T
2. Isomorphic graphs have the same eigenvalues
3. Algorithm: Compute eigenvalues of both adjacency matrices and compare
4. Eigenvalue computation can be done in polynomial time
5. Therefore, graph isomorphism can be tested in polynomial time

**The Critical Error**:

The implication only works in one direction:
- Isomorphic graphs → Same eigenvalues ✓
- Same eigenvalues → Isomorphic graphs ✗

**Counterexample**: There exist 180 pairwise non-isomorphic graphs in SRG(36, 14, 4, 6) that all have identical eigenvalues.

**Formalization Goal**:

The Lean and Rocq formalizations in this folder demonstrate:
1. That eigenvalue equality is a necessary but not sufficient condition for isomorphism
2. The existence of non-isomorphic cospectral graphs (strongly regular graphs)
3. Why the algorithm produces false positives
4. That no simple fix makes this approach work

## Implementation Notes

The formalizations follow the structure of the original papers as closely as possible, inserting comments at each step that:
- Quotes the original text
- Translates to formal statements
- Identifies where compilation fails or where `sorry` is needed
- Explains why the step cannot be completed

This preserves the maximum information about where each argument breaks down.
