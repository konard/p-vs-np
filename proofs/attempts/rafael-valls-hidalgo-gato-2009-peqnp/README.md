# Rafael Valls Hidalgo-Gato (2009) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #51](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 51 (from Woeginger's list)
- **Author**: Rafael Valls Hidalgo-Gato
- **Year**: 2009 (original work from 1985)
- **Claim**: P = NP
- **Method**: Polynomial-time algorithm for solving systems of equations over Galois fields
- **Status**: Refuted (encoding complexity barrier)

---

## Summary

Rafael Valls Hidalgo-Gato claimed to prove P=NP based on a polynomial-time algorithm for solving systems of simultaneous equations over Galois fields (finite fields). The approach involved:

1. Developing a method to solve polynomial equation systems over finite fields
2. Encoding NP-complete problems (like SAT) as such equation systems
3. Claiming the combined process runs in polynomial time
4. Concluding P=NP

**The Error:** The approach fails due to the fundamental **encoding complexity barrier** - when encoding NP-complete problems as Galois field equations, there is an unavoidable tradeoff between:
- Encoding size (number of variables and equations)
- Polynomial degree
- Solving difficulty

No polynomial-size, low-degree encoding exists that can be solved in polynomial time (unless P=NP, making the argument circular).

---

## The Approach

### Core Idea

**Galois Fields** (finite fields GF(q)) have efficient arithmetic for linear algebra:
- Gaussian elimination solves linear systems in O(n³) time
- This is genuinely polynomial and well-established

**Encoding NP Problems:**
- SAT and other NP-complete problems CAN be encoded as polynomial equations over GF(2)
- Standard encoding: Boolean variable x becomes x² - x = 0 (forces x ∈ {0,1})
- Clause (x₁ ∨ x₂ ∨ ... ∨ xₖ) becomes (1-x₁)(1-x₂)...(1-xₖ) = 0

**The Claim:**
- If these equations can be solved in polynomial time
- And the encoding is polynomial-size
- Then P = NP

### Why It Seems Plausible

- Galois field arithmetic IS efficient for linear systems
- SAT DOES encode as polynomial equations
- The mathematical framework is elegant and well-understood

---

## The Error: Encoding Complexity Barrier

### The Fundamental Tradeoff

When encoding SAT over GF(2), you face an inescapable choice:

| Encoding Strategy | Variables | Equations | Degree | Solvable in Poly Time? |
|---|---|---|---|---|
| **Standard Encoding** | O(n) | O(m) | **O(n)** worst case | ❌ No (high degree) |
| **Linearization** | **O(2ⁿ)** | **O(2ⁿ)** | O(1) | ❌ No (exponential size) |
| **Large Field GF(2ⁿ)** | O(n) | O(m) | O(1) | ❌ No (field arithmetic expensive) |

**There is no fourth option** that achieves:
- Polynomial number of variables
- Polynomial number of equations
- Low (constant) degree
- Small field size

### Known Complexity Results

**What DOES work (Polynomial Time):**
- Linear systems over GF(q): O(n³) via Gaussian elimination ✓
- Very special structured polynomial systems ✓

**What DOESN'T work (NP-Hard or worse):**
- Quadratic systems over GF(2): NP-complete ❌
- Degree-d polynomial systems (d ≥ 2): NP-hard or worse ❌
- General polynomial ideal membership: Exponential lower bounds ❌

### The Circular Reasoning

The claim essentially assumes:
1. "We can solve polynomial systems in polynomial time"
2. "Therefore we can solve NP-complete problems in polynomial time"
3. "Therefore P = NP"

**The problem:** Step 1 is itself equivalent to P=NP (since solving polynomial systems over finite fields IS NP-complete for degree ≥ 2).

**Cannot assume P=NP to prove P=NP!**

---

## Contents

- [`ORIGINAL.md`](ORIGINAL.md) - Information about the 1985 and 2009 papers (not publicly available)
- [`proof/`](proof/) - Forward proof formalization following the claimed approach
  - [`proof/README.md`](proof/README.md) - Explanation of the forward proof
  - [`proof/lean/VallsProof.lean`](proof/lean/VallsProof.lean) - Lean 4 formalization
  - [`proof/rocq/VallsProof.v`](proof/rocq/VallsProof.v) - Rocq formalization
- [`refutation/`](refutation/) - Formalization of why the proof fails
  - [`refutation/README.md`](refutation/README.md) - Detailed explanation of the errors
  - [`refutation/lean/VallsRefutation.lean`](refutation/lean/VallsRefutation.lean) - Lean 4 refutation
  - [`refutation/rocq/VallsRefutation.v`](refutation/rocq/VallsRefutation.v) - Rocq refutation

---

## Key Lessons

1. **Encoding Complexity Matters**: The cost of converting problems to a solvable form is part of the total complexity
2. **Tradeoffs Are Fundamental**: Reducing degree increases size; reducing size increases degree; no escape
3. **Linear ≠ Polynomial**: Gaussian elimination works for linear systems, but this efficiency doesn't extend to nonlinear (degree ≥ 2) systems
4. **Circular Reasoning**: Assuming polynomial-time solvability of NP-hard equation systems is assuming P=NP

---

## References

### Original Works (Unavailable)

1. **Valls Hidalgo-Gato, R.** (1985). "Método de solución para sistemas de ecuaciones simultáneas sobre un Campo de Galois y aplicaciones en Inteligencia Artificial." ININTEF Scientific Conference, 1985 Annual Report, Vol.II, S2-25, p.274, Havana, Cuba.

2. **Valls Hidalgo-Gato, R.** (2009). "P=NP." ICIMAF Technical Report, ISSN 0138-8916, March 2009.

3. **Announcement:** comp.theory usenet newsgroup, March 2009.

### Background Literature

4. **Buchberger, B.** (1965). "Ein Algorithmus zum Auffinden der Basiselemente." PhD thesis. (Gröbner basis method)

5. **Fraenkel, A. S., & Yesha, Y.** (1979). "Complexity of solving algebraic equations." *Information Processing Letters*, 10(4-5): 178-179.

6. **Mayr, E. W., & Meyer, A. R.** (1982). "The complexity of the word problems for commutative semigroups and polynomial ideals." *Advances in Mathematics*, 46(3): 305-329. (Exponential lower bounds)

7. **Lidl, R., & Niederreiter, H.** (1997). *Finite Fields.* Cambridge University Press. (Comprehensive Galois field reference)

8. **Cox, D., Little, J., & O'Shea, D.** (2007). *Ideals, Varieties, and Algorithms.* Springer. (Computational algebraic geometry)

---

**Related:** [Issue #456](https://github.com/konard/p-vs-np/issues/456) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
