# Yann Dujardin (2009) - P=NP Proof Attempt

**Attempt ID**: 52 (Woeginger's list)
**Author**: Yann Dujardin
**Year**: 2009
**Claim**: P = NP
**arXiv**: [0909.3466v2](http://arxiv.org/abs/0909.3466)
**Status**: **WITHDRAWN** - Author withdrew the paper in December 2010

## Summary

In September 2009, Yann Dujardin submitted a paper claiming to prove P = NP by providing a polynomial-time algorithm for the NP-complete PARTITION problem. The paper, titled "Résolution du partition problem par une approche arithmétique" (Resolution of the partition problem by an arithmetic approach), was written in French.

## Known Error

**The author himself withdrew the paper**, stating:

> "This paper has been withdrawn by Yann Dujardin due to a crucial error (in one of the quadratic forms introduced)."

This withdrawal notice appears on the arXiv page for version 3 (December 3, 2010).

## Main Approach

The paper attempts to solve the PARTITION problem through an arithmetic/geometric approach:

### 1. Reduction to Binary Linear Equation

Dujardin reduces the PARTITION problem to solving a **binary linear equation**:
- Given set S = {a₁, ..., aₙ} ⊂ ℤⁿ
- Find partition where ∑(a ∈ S₁) a = ∑(a ∈ S₂) a
- This is equivalent to solving: (2a₁, ..., 2aₙ)x = ∑aⱼ where x ∈ {0,1}ⁿ

### 2. General Diophantine Linear Equation Resolution

The paper first develops theory for solving general linear Diophantine equations ax = b where x ∈ ℤⁿ:

- **Theorem 1**: Characterizes solution space using GCD sequence P₁, P₂, ..., Pₙ
  - Pₖ = gcd(a₁, ..., aₖ)
  - Solution exists iff Pₙ divides b
  - Solution space: {xᵖ + Mx' | x' ∈ ℤⁿ⁻¹} for a particular solution xᵖ and resolution matrix M

- Uses **Extended Euclidean Algorithm** to construct solutions

### 3. Geometric Approach to Binary Solutions

The core of the claimed polynomial algorithm involves:

- **Affine space Eₐ**: n-dimensional real affine space
- **Hypercube C**: Points with coordinates in [0,1]
- **Hyperplane H**: Defined by equation aX = b
- **Vertices S**: Points of C with coordinates in {0,1}

**Key Idea** (Theorem-Definition 3):
- Let O be the center of hypercube (coordinates all 1/2)
- Let Pᵣₑf be orthogonal projection of O onto H
- Binary equation has solution iff the closest ℤⁿ⁻¹-lattice point to Pᵣₑf (in coordinates on H) is a vertex of C

### 4. The Algorithm (AD - Algorithme Diophantien)

**Input**: Binary linear equation ax = b with x ∈ {0,1}ⁿ

**Steps**:
1. Compute GCDs: Pₖ = gcd(a₁,...,aₖ) for k=1..n (using Euclidean algorithm)
2. Check if Pₙ divides b (if not, no solution)
3. Construct resolution matrix M using Extended Euclidean Algorithm
4. Compute reference point Xᵣₑf = coordinates of Pᵣₑf in canonical frame
5. Transform to hyperplane coordinates: X'ᵣₑf = (Mₜ)⁻¹((Xᵣₑf)ₜ - Xᵖₜ)
6. Round to nearest integers: X*' = A(X'ᵣₑf)
7. Transform back: X* = Xᵖ + MX*'
8. Check if X* ∈ {0,1}ⁿ

**Claimed Complexity**: O(n⁴ ln²(max(|b|, maxⱼ|aⱼ|)))

### 5. Conclusion

**Corollary 4** claims: "This implies P = NP"

## The Error Location

While the author withdrew the paper citing "a crucial error in one of the quadratic forms introduced," the specific location is likely in:

1. **The geometric construction** (Section 4.3-4.4): The mapping between:
   - Euclidean distance in the hyperplane H
   - Integer lattice points in the coordinate system Rₕ
   - Vertices of the hypercube C

2. **The rounding procedure** (Corollary-Definition 2): The function A that rounds coordinates may not preserve the property of being a hypercube vertex.

3. **Lemma 1 and its application**: The characterization of vertices S as exactly those ℤ-lattice points at distance √(n/4) from O may have subtle issues when combined with the coordinate transformation.

The error is likely that the **closest lattice point in the hyperplane coordinate system does NOT necessarily correspond to the closest vertex** of the original hypercube. The coordinate transformation via matrix M may distort distances in a way that invalidates the geometric argument.

## Formalization Goal

Our formalization aims to:

1. Formalize the reduction from PARTITION to binary linear equations (Section 2)
2. Formalize the diophantine equation theory (Section 3)
3. Formalize the geometric setup (Section 4.1-4.2)
4. **Identify the precise gap** in the proof of Theorem-Definition 3 or its application
5. Show where the polynomial-time claim breaks down

## Key Definitions to Formalize

- Linear Diophantine equations and their solution spaces
- Binary linear equations (solutions in {0,1}ⁿ)
- Resolution matrix M
- Affine space structure and hyperplane H
- Distance computations and nearest lattice points
- The rounding function A and its properties

## References

- Original paper: arXiv:0909.3466v2 (21 Sep 2009)
- Withdrawal notice: arXiv:0909.3466v3 (3 Dec 2010)
- Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- PARTITION problem: Karp (1972), "Reducibility Among Combinatorial Problems"
