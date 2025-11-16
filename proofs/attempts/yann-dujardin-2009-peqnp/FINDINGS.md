# Findings: Dujardin (2009) P=NP Attempt

## Executive Summary

Yann Dujardin's 2009 paper claimed to prove P=NP by providing a polynomial-time algorithm for the PARTITION problem. **The author himself withdrew the paper in December 2010**, citing "a crucial error in one of the quadratic forms introduced."

## The Approach

### Valid Components

1. **Reduction to Binary Linear Equation** (Section 2, pages 2-4)
   - Correctly reduces PARTITION to solving ax = b where x ∈ {0,1}ⁿ
   - The reduction is polynomial and correct
   - Formula: (2a₁,...,2aₙ)x = ∑aⱼ

2. **Diophantine Equation Theory** (Section 3, pages 4-11)
   - **Theorem 1**: Characterizes the solution space of linear Diophantine equations
   - Uses GCD sequences and resolution matrices
   - Based on Extended Euclidean Algorithm
   - This theory is mathematically sound in principle

### The Fatal Flaw

The error occurs in **Section 4: Resolution of Binary Linear Equations** (pages 11-30), specifically in the geometric argument.

#### The Flawed Claim (Theorem-Definition 3, pages 14-18)

Dujardin claims:
> A binary linear equation ax = b has a solution if and only if the closest ℤⁿ⁻¹-lattice point to Pᵣₑf (the projection of the hypercube center onto the hyperplane) **in hyperplane coordinates** is a vertex of the hypercube.

#### Why This Fails

1. **Coordinate Transformation Issue**:
   - The resolution matrix M transforms from hypercube coordinates to hyperplane coordinates
   - This transformation is **NOT distance-preserving** in the required sense
   - Nearest integer point in transformed coordinates ≠ nearest vertex in original space

2. **The Missing Link**:
   - The paper assumes: nearest lattice point in H-coordinates → binary solution
   - Reality: nearest lattice point in H-coordinates → integer Diophantine solution
   - But: integer Diophantine solution ≠ binary solution (values not guaranteed to be in {0,1})

3. **Quadratic Form Error**:
   - The author mentions "error in one of the quadratic forms"
   - This likely refers to the distance computations: d(P,Q)² = ∑(pᵢ - qᵢ)²
   - When coordinates are transformed via M, the distance formula becomes more complex
   - The paper treats it as if Euclidean distance is preserved, but it's not

#### Specific Problem Location

**Page 15, Lemma 1**:
```
S = {P ∈ Eₐ | P is an ℝ-lattice point and d(P,O)² = n/4}
```

This characterizes vertices as points at specific distance from center O.

**Pages 17-18, Proof of Theorem-Definition 3**:
The proof assumes that if P* is the closest ℝᶻₕ-point to Pᵣₑf, then:
- If P* ∈ S (is a vertex), then solution exists
- If P* ∉ S (not a vertex), then no solution exists

**The Gap**: The coordinate transformation M changes how distances are measured. A point that is "closest" in the transformed coordinate system may not correspond to the actual closest vertex in the original hypercube.

## The Algorithm (AD - Algorithme Diophantien)

### Structure (Pages 23-25)

1. Compute GCD sequence using Euclidean algorithm: O(n log max_a)
2. Construct resolution matrix M via Extended Euclidean: O(n³ log² max_a)
3. Compute reference point Xᵣₑf: O(n² log² max_a)
4. Transform to hyperplane coordinates: O(n³ log² max_a)
5. **Round to nearest integers**: O(n³ log² max_a)
6. Transform back and check: O(n⁴ log² max_a)

### The Rounding Step is the Problem

**Page 25, Corollary-Definition 2**: Defines function A that rounds each coordinate to nearest integer.

**Issue**: This rounding assumes that:
- Nearest integer in each coordinate → nearest lattice point overall
- Nearest lattice point → hypercube vertex

Both assumptions are FALSE due to the coordinate transformation.

## Complexity Analysis (Pages 26-32)

The claimed complexity of O(n⁴ log²(max(|b|, max|aⱼ|))) is correct **for the algorithm as described**.

However, the algorithm **does not correctly solve the PARTITION problem** due to the geometric flaw.

## What the Paper Actually Proves

If we accept the (flawed) geometric claim, the paper would show:
- Certain linear Diophantine equations can be solved in polynomial time ✓
- GCD-based algorithms have nice structure ✓
- **Binary linear equations can be solved in polynomial time ✗ FALSE**

## Why P≠NP Remains Open

The withdrawal of this paper does not affect the P vs NP question because:
1. The geometric claim (Theorem-Definition 3) is incorrect
2. The rounding procedure doesn't preserve the vertex property
3. No valid polynomial-time algorithm for PARTITION was actually demonstrated
4. PARTITION remains NP-complete

## Formalization Notes

Our formalizations in Coq, Lean, and Isabelle:

1. **Correctly formalize** the PARTITION reduction
2. **Sketch** the Diophantine equation theory (full formalization would be extensive)
3. **Identify the critical claim** as an axiom
4. **Prove** that if the critical claim is false (as it is), the P=NP conclusion is invalid
5. **Document** where the geometric argument breaks down

## Lessons for P vs NP Attempts

This attempt illustrates a common pitfall:

- **Coordinate transformations** can distort geometric properties
- **Distance preservation** must be carefully verified
- **Rounding procedures** don't automatically preserve discrete properties
- **Geometric intuition** in high dimensions can be misleading

The fact that the author himself recognized and withdrew the error demonstrates intellectual honesty and proper scientific practice.

## References

- Dujardin, Y. (2009). "Résolution du partition problem par une approche arithmétique". arXiv:0909.3466v2.
- Withdrawal notice: arXiv:0909.3466v3 (3 December 2010).
- Karp, R. M. (1972). "Reducibility Among Combinatorial Problems". Complexity of Computer Computations.
