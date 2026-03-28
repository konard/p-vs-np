# Narendra S. Chaudhari (2009) - Refutation

## Why the Proof Fails

Chaudhari's 2009 P=NP attempt was based on a **clause-based representation** approach. The proof claimed:

1. 3-SAT can be solved using clauses as fundamental computational units
2. An O(n^13) algorithm exists using this representation
3. Therefore, P=NP

The proof fails because **representation changes cannot alter computational complexity**.

## The Core Error

### The Invalid Representation Argument

Chaudhari's approach claimed:

> By using clauses instead of literals as the fundamental units, we can solve 3-SAT in polynomial time.

This is **logically invalid** because:

1. **Information preservation**: Any valid representation must encode the same information
   - A 3-SAT instance requires Θ(m) space for m clauses
   - Whether we index by literals or clauses doesn't change the problem difficulty

2. **Exponential mapping is irrelevant**: While there are O(n³) possible 3-clauses over n variables:
   - A specific instance only uses m clauses (typically m = O(n))
   - The existence of unused clauses provides no computational advantage
   - This is similar to saying: "There are 2^n possible truth assignments, so we can check them all efficiently"

3. **Hidden complexity**: For the algorithm to be correct AND polynomial:
   - It must handle all possible 3-SAT instances
   - All operations, including representation conversion, must be polynomial
   - Any exponential hidden costs invalidate the claim

### Analogy: Graph Representations

Consider graph algorithms with different representations:
- **Adjacency matrix**: O(n²) space, some operations easier
- **Adjacency list**: O(n + m) space, other operations easier
- **Edge list**: O(m) space, different trade-offs

Despite these differences:
- The computational complexity class of graph problems (e.g., Hamiltonian Cycle is NP-complete)
- Remains the same regardless of representation
- Representation affects constant factors and specific algorithm efficiency
- But does NOT change the fundamental complexity class

Similarly, switching from literals to clauses in 3-SAT cannot make an NP-complete problem polynomial.

## The Missing Proofs

For the claim to be valid, the following would need to be rigorously proven:

### 1. Correctness

```
∀ φ ∈ 3-SAT. Algorithm(φ) = "SAT" ↔ ∃ assignment. assignment satisfies φ
```

This requires:
- Proof that the algorithm accepts all satisfiable instances
- Proof that the algorithm rejects all unsatisfiable instances
- Verification for edge cases and adversarial constructions

The paper likely lacks this complete correctness proof.

### 2. Polynomial Time Complexity

```
∃ k. ∀ φ. Time(Algorithm, φ) ≤ |φ|^k
```

This requires:
- Analysis of every operation in the algorithm
- Including representation conversion costs
- Accounting for all possible instance structures
- Proving the O(n^13) bound rigorously

The paper likely lacks this complete complexity analysis.

### 3. Representation Conversion Analysis

```
Time(ConvertToClauseBased, φ) + Time(Algorithm, φ) ≤ |φ|^k
```

If the conversion is exponential, the overall algorithm is exponential.

## Why Representation Changes Cannot Help

### Fundamental Principle: Computational Equivalence

All reasonable computational models are polynomially equivalent:
- Turing machines
- Random Access Machines (RAM)
- Lambda calculus
- Register machines

Similarly, all reasonable representations of a problem are polynomially equivalent:
- Different data structures
- Different encodings
- Different indexing schemes

**Changing representation can affect constant factors, but cannot change complexity classes.**

### The Complexity is Intrinsic

3-SAT's difficulty is intrinsic to the problem:
- Determining satisfiability requires resolving exponential search space
- No representation change eliminates this fundamental difficulty
- The problem remains NP-complete regardless of how it's encoded

## Formal Refutation

The formalizations in this directory (`lean/` and `rocq/`) demonstrate:

1. **`representation_preserves_complexity`**: Representation changes preserve computational complexity

2. **`correctness_unproven`**: The algorithm's correctness for all inputs is not established

3. **`polynomial_time_unproven`**: The polynomial time bound is not rigorously proven

4. **`claim_does_not_imply_p_eq_np`**: Without correctness and complexity proofs, the claim is invalid

## Known Context

### Why 3-SAT is Hard

The difficulty of 3-SAT is well-established:

1. **Cook-Levin Theorem (1971)**: 3-SAT is NP-complete
2. **Exponential Time Hypothesis (ETH)**: No 2^o(n) time algorithm exists
3. **Decades of research**: No polynomial algorithm found despite extensive effort
4. **Best known algorithms**: DPLL, CDCL still require exponential time in worst case

### Pattern of Representation-Based Attempts

Many P=NP attempts claim to solve via representation changes:
- Binary Decision Diagrams (BDDs) - can be exponential size
- Algebraic formulations - preserve complexity
- Geometric mappings - preserve complexity
- Graph-theoretic encodings - preserve complexity

All fail for the same fundamental reason: **representation does not change computational complexity**.

## Barriers Not Addressed

The paper does not address known barriers to proving P=NP:

- **Relativization** (Baker-Gill-Solovay, 1975): Many proof techniques fail relative to oracles
- **Natural Proofs** (Razborov-Rudich, 1997): Certain classes of proofs cannot work
- **Algebrization** (Aaronson-Wigderson, 2008): Algebraic techniques have limitations

Any valid P=NP proof must overcome at least some of these barriers.

## Conclusion

The refutation is straightforward:

1. Representation changes preserve computational complexity
2. The algorithm's correctness is not rigorously proven
3. The polynomial time bound is not rigorously established
4. Without these proofs, the claim of P=NP is unsubstantiated

The formalization makes this gap explicit and demonstrates why the clause-based representation argument is insufficient.

## References

- Woeginger's P vs NP page, Entry #59
- Cook, S. A. (1971). "The complexity of theorem proving procedures"
- Garey, M. R., & Johnson, D. S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness"
