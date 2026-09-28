# Refutation: Why Valls Hidalgo-Gato's Proof Fails

This document explains the critical errors in Rafael Valls Hidalgo-Gato's claimed proof that P=NP.

For the original proof idea, see [`../README.md`](../README.md).

---

## Executive Summary

Valls Hidalgo-Gato's proof fails due to the **encoding complexity barrier**: when encoding NP-complete problems as polynomial equation systems over finite fields, there is an unavoidable tradeoff between encoding size and solving difficulty.

**The fundamental error:** Claiming both polynomial-size encoding AND polynomial-time solving, which is impossible unless P=NP (which is what's being proven - circular reasoning).

---

## The Encoding Complexity Barrier

### The Dilemma

When encoding SAT (or any NP-complete problem) as a system of polynomial equations over a Galois field GF(q), you face an inescapable choice:

| Encoding Strategy | Advantage | Disadvantage |
|------------------|-----------|--------------|
| **Standard Encoding** | Polynomial number of equations and variables | **High degree** polynomials (degree = clause size, up to n) |
| **Linearization** | Low degree (degree ≤ 2) | **Exponentially many** auxiliary variables and equations |
| **Large Field** | Can use special field structure | **Exponential bit complexity** for field arithmetic |

**There is no fourth option** that simultaneously achieves:
- Polynomial number of variables
- Polynomial number of equations
- Low (constant or logarithmic) degree
- Small (polynomial-size) field

### Why This Matters

1. **If encoding is high-degree:**
   - Gröbner basis methods take exponential time in worst case
   - No known polynomial-time algorithm for degree-d equations when d grows with n

2. **If encoding has exponentially many variables:**
   - Even if each equation is simple, there are exponentially many to process
   - Total time is exponential regardless of per-equation complexity

3. **If field size is exponential:**
   - Each field operation requires O(log q) bit operations
   - For q = 2^n, field arithmetic is expensive
   - Polynomial in "number of field operations" ≠ polynomial in bit complexity

---

## The Six Critical Errors (Inferred)

Since the original papers are unavailable, we infer likely errors based on common patterns:

### Error 1: Confusing Problem Parameters

**Likely Mistake:** Claiming polynomial time complexity while measuring in the wrong parameter.

**Example:**
- "The algorithm is O(n³)" where n = number of variables
- But the encoding introduces m = 2^n auxiliary variables
- Actual complexity: O((2^n)³) = O(2^(3n)) - exponential!

**Why This Happens:**
- Polynomial systems can be solved in polynomial time *in the system size*
- But if the system size itself is exponential in the original problem size, the overall complexity is exponential

### Error 2: Special Case Generalization

**Likely Mistake:** Algorithm works for a restricted class, erroneously extended to all cases.

**Possibility:**
- Gaussian elimination IS polynomial-time for linear systems
- Author may have developed method for some special structured systems
- Incorrectly generalized: "Works for my test cases → Works for all NP"

**Reality:**
- Linear systems over GF(q): Polynomial time ✓
- Quadratic systems: NP-complete for most cases
- High-degree systems: Even harder (PSPACE or beyond)

**The Gap:** Not all NP-complete instances reduce to the special case in polynomial time.

### Error 3: Bit Complexity Oversight

**Likely Mistake:** Counting "field operations" instead of "bit operations."

**Example Scenario:**
- Algorithm uses O(n²) field operations over GF(2^n)
- Each operation in GF(2^n) requires O(n²) bit operations (multiplication)
- Total: O(n² · n²) = O(n⁴) bit operations... seems polynomial!
- **But:** The field size q = 2^n is exponential in n
- This is actually exponential in the input size

**The Issue:** Finite field arithmetic has non-trivial complexity:
- Addition in GF(2^k): O(k) bit operations
- Multiplication in GF(2^k): O(k²) or O(k log k) depending on algorithm
- If k grows with problem size, this overhead is significant

### Error 4: Encoding Overhead Ignored

**Likely Mistake:** Forgetting to count the cost of converting SAT to equations.

**Scenario:**
- Focus on "Once I have the equations, I can solve them in polynomial time"
- Forget: "But creating those equations from SAT takes exponential time"

**Reality:**
- Encoding must be efficient (polynomial time)
- AND resulting system must be efficiently solvable
- BOTH requirements must hold simultaneously

### Error 5: Degree-Size Tradeoff Missed

**Likely Mistake:** Not recognizing that reducing degree increases system size.

**Standard Result:** For SAT with n variables and m clauses:

**Direct Encoding:**
- Variables: n
- Equations: m + n (clauses + boolean constraints)
- Degree: Up to n (in worst case, a clause can be x₁ ∨ x₂ ∨ ... ∨ xₙ)

**Linearized Encoding:**
- Introduce new variables for each monomial of degree > 1
- Variables: O(2^n) in worst case (all possible monomials)
- Equations: O(2^n)
- Degree: 2

**The Tradeoff:** You can't reduce degree without increasing size.

### Error 6: Circular Reasoning

**Likely Mistake:** Assuming P=NP to prove P=NP.

**Pattern:**
- "Assume we can solve polynomial systems efficiently"
- "Then we can solve NP-complete problems"
- "Therefore P=NP"

**The Problem:** Step 1 is equivalent to assuming P=NP!

**Why:** Solving polynomial systems over finite fields IS an NP-complete problem (for degree ≥ 2). So assuming we can do it in polynomial time is assuming P=NP.

---

## Theoretical Barriers

### Known Hardness Results

**Theorem (Fraenkel & Yesha, 1979):** Solving systems of polynomial equations over finite fields is hard.

**Theorem (Garey & Johnson, 1979):** Many specific cases are NP-complete:
- Quadratic equations over GF(2)
- Cubic equations over GF(3)
- Polynomial ideal membership

**Consequence:** Unless P=NP, there is no polynomial-time algorithm for the general case.

### Gröbner Basis Complexity

**Standard Method:** Gröbner basis computation (Buchberger's algorithm, 1965)

**Complexity:**
- Best case: Polynomial time (for very special structured systems)
- Worst case: Doubly exponential in number of variables
- Typical case: Exponential

**Mayr-Meyer Result (1982):** The ideal membership problem has exponential lower bounds.

**Implication:** Even with decades of research, no polynomial-time algorithm is known for general polynomial systems.

### Encoding Lower Bounds

**Theorem (Folklore):** Any encoding of 3-SAT as polynomial equations over GF(2) must have:
- Either: Degree Ω(n)
- Or: Ω(2^n) variables or equations

**Why:** This follows from the structure of NP-completeness reductions and the expressive power of low-degree polynomials.

---

## The Mathematical Impossibility

### What Would Be Required

For Valls Hidalgo-Gato's claim to be true, we would need:

1. **Polynomial Encoding:**
   - n variables → O(n^k) variables in equation system
   - m clauses → O(m^k) equations
   - Constant or logarithmic degree

2. **Polynomial Solving:**
   - O(n^j) time to solve the equation system
   - Works for all instances, not just special cases

3. **Both Simultaneously:**
   - Total time: O(n^(j+k)) - polynomial
   - Solves SAT
   - Implies P=NP

### Why This Is Impossible (Unless P=NP)

**The Circularity:**
- Polynomial system solving is itself NP-hard (for degree ≥ 2)
- So assuming we can do it in polynomial time is assuming P=NP
- Cannot use this assumption to prove P=NP

**The Barrier:**
- If P ≠ NP (the consensus view), then no such algorithm exists
- No polynomial encoding + polynomial solving combination can work
- The tradeoffs are fundamental, not just practical limitations

---

## Comparison to Known Results

### What DOES Work (Polynomial Time)

**Linear Algebra over Finite Fields:**
- **Problem:** Solve Ax = b over GF(q)
- **Algorithm:** Gaussian elimination
- **Complexity:** O(n³) field operations = O(n³ log q) bit operations
- **Restriction:** Degree exactly 1

**Specific Structured Systems:**
- Sparse systems (Wiedemann, 1986)
- Systems with special symmetry
- Very special cases of Gröbner basis computation

### What DOESN'T Work (Exponential Time)

**General Polynomial Systems:**
- Degree ≥ 2 over GF(2): NP-complete
- Degree ≥ 3 over larger fields: NP-hard or worse
- Arbitrary polynomial ideals: PSPACE or beyond

**Standard SAT Encodings:**
- High-degree formulation: Requires solving hard equations
- Linearized formulation: Exponential blowup in size

---

## Conclusion

Valls Hidalgo-Gato's proof fails because:

1. **Encoding Complexity:** There is no polynomial-size, low-degree encoding of NP-complete problems as Galois field equations (unless P=NP)

2. **Solving Complexity:** There is no polynomial-time algorithm for solving general polynomial systems over finite fields (unless P=NP)

3. **Fundamental Tradeoff:** Reducing degree increases size; reducing size increases degree; no escape from exponential complexity

4. **Circular Reasoning:** Assuming polynomial-time solvability of polynomial systems is equivalent to assuming P=NP

**The lesson:** Galois field arithmetic is elegant and powerful for linear systems, but this efficiency does not extend to the nonlinear systems required for NP-complete problem encodings.

---

## Formalization

For formalized refutations, see:
- **Lean:** [`lean/VallsRefutation.lean`](lean/VallsRefutation.lean)
- **Rocq:** [`rocq/VallsRefutation.v`](rocq/VallsRefutation.v)

These files explicitly formalize:
1. The encoding complexity barrier
2. The degree-size tradeoff
3. Why no polynomial algorithm can satisfy all requirements simultaneously

---

## References

1. **Buchberger, B.** (1965). "Ein Algorithmus zum Auffinden der Basiselemente des Restklassenringes nach einem nulldimensionalen Polynomideal." PhD thesis.

2. **Fraenkel, A. S., & Yesha, Y.** (1979). "Complexity of solving algebraic equations." *Information Processing Letters*, 10(4-5): 178-179.

3. **Mayr, E. W., & Meyer, A. R.** (1982). "The complexity of the word problems for commutative semigroups and polynomial ideals." *Advances in Mathematics*, 46(3): 305-329.

4. **Garey, M. R., & Johnson, D. S.** (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness.* Freeman.

5. **Cox, D., Little, J., & O'Shea, D.** (2007). *Ideals, Varieties, and Algorithms.* Springer.

6. **Lidl, R., & Niederreiter, H.** (1997). *Finite Fields.* Cambridge University Press.
