# Refutations

This folder contains formal refutations of the claims made in Delacorte and Czerwinski's papers.

## Refutation of Delacorte's Claim

**Claim**: Graph Isomorphism is PSPACE-complete

**Refutation Arguments**:

### 1. Conflation of Equivalence and Isomorphism

**Theorem**: The reduction chain from regular expression equivalence to graph isomorphism is invalid.

**Proof**:
- Regular expression equivalence ≡ finite automaton equivalence (standard result)
- Finite automaton equivalence is PSPACE-complete (Meyer & Stockmeyer, 1972)
- Finite automaton isomorphism ≡_p graph isomorphism (Booth, 1978)
- **BUT**: Automaton equivalence ≠ automaton isomorphism
- Therefore: The reduction does not establish PSPACE-hardness of GI

**Key Insight**: Booth's result shows that testing if two automata are **structurally identical** (isomorphic) is polynomial-time equivalent to GI. But the PSPACE-complete problem is testing if two automata **accept the same language** (equivalent).

### 2. Known Complexity Upper Bounds

**Theorem**: Graph isomorphism has polynomial-time upper bounds that contradict PSPACE-completeness.

**Evidence**:
- GI ∈ NP (Obvious: certificate is the isomorphism)
- GI ∈ co-AM (Goldreich-Micali-Wigderson, 1991)
- GI ∈ Quasi-P (Babai, 2016): O(exp(log^c n)) time
- If GI were PSPACE-complete, then NP = PSPACE (widely believed false)

### 3. Structural Properties

**Theorem**: Graph isomorphism lacks the structural properties of PSPACE-complete problems.

**Key Properties PSPACE-complete problems have**:
- Require exponential space in deterministic models
- Often involve quantifier alternation (TQBF, QBF)
- Capture full power of polynomial space

**Why GI doesn't fit**:
- Can be solved with polynomial space (it's in NP ⊆ PSPACE)
- No known encoding of quantifier alternation
- Best known algorithms use very different techniques than PSPACE-complete problems

## Refutation of Czerwinski's Claim

**Claim**: Graph Isomorphism can be solved in polynomial time via eigenvalue comparison

**Refutation Arguments**:

### 1. Counterexample: Non-Isomorphic Cospectral Graphs

**Theorem**: There exist non-isomorphic graphs with identical eigenvalue spectra.

**Proof by Construction**:
- Consider strongly regular graphs SRG(n, k, a, c)
- All graphs in SRG(n, k, a, c) have the same eigenvalues (Godsil & Royle, 2001)
- There exist 180 pairwise non-isomorphic graphs in SRG(36, 14, 4, 6) (McKay & Spence, 2001)
- Therefore: eigenvalue equality does not imply isomorphism

**Example**: The 180 graphs in SRG(36, 14, 4, 6) all have eigenvalue spectrum:
- λ₁ = 14 (multiplicity 1)
- λ₂ = 2 (multiplicity 20)
- λ₃ = -4 (multiplicity 15)

Yet no two of these graphs are isomorphic.

### 2. Necessary vs. Sufficient Conditions

**Theorem**: Eigenvalue equality is necessary but not sufficient for graph isomorphism.

**Proof**:
- (⇒) If G₁ ≅ G₂, then spec(G₁) = spec(G₂)
  - Isomorphism gives permutation matrix P with A₂ = P A₁ P^T
  - Similar matrices have the same eigenvalues
  - Therefore: isomorphic graphs have the same spectrum ✓

- (⇐) If spec(G₁) = spec(G₂), then G₁ ≅ G₂?
  - **FALSE**: See counterexample above
  - Eigenvalues only capture partial structural information
  - Different graph structures can have the same spectrum

### 3. Algorithm Incorrectness

**Theorem**: The eigenvalue-based algorithm produces false positives.

**Proof**:
- Algorithm: Return "isomorphic" if spec(G₁) = spec(G₂)
- By counterexample: ∃G₁, G₂ with spec(G₁) = spec(G₂) but G₁ ≇ G₂
- Therefore: Algorithm returns "isomorphic" for non-isomorphic graphs
- This is a **false positive**: Algorithm claims isomorphism when none exists

**No Simple Fix**: Adding more spectral invariants doesn't solve the problem:
- Any polynomial-time computable graph invariant can fail to distinguish non-isomorphic graphs
- This is a fundamental limitation, not a implementation bug

## Czerwinski's Self-Retraction

In October 2022, Czerwinski himself published a retraction acknowledging the error:

> "In the paper 'A Polynomial Time Algorithm for Graph Isomorphism' we claimed, that there is a polynomial algorithm to test if two graphs are isomorphic. But the algorithm is wrong. It only tests if the adjacency matrices of two graphs have the same eigenvalues. There is a counterexample of two non-isomorphic graphs with the same eigenvalues."

This is a rare and commendable example of an author formally retracting their own incorrect P vs NP attempt.

## Combined Refutation

**Theorem**: If both claims were true, we would have P = PSPACE, which is widely believed to be false.

**Proof**:
- Assume Delacorte's claim: GI is PSPACE-complete
- Assume Czerwinski's claim: GI ∈ P
- Then: P = PSPACE (every PSPACE problem reduces to GI, which is in P)
- This would collapse the polynomial hierarchy: P = NP = co-NP = ... = PSPACE
- Community consensus: This is extremely unlikely
- Therefore: At least one (and likely both) claims must be false

## Formalization Notes

The Lean and Rocq files in this folder provide machine-checked proofs of the key refutation theorems. Where full formalization is not possible (e.g., referencing external empirical results), we use axioms with clear documentation.
