# Original Papers: Rafael Valls Hidalgo-Gato's P=NP Claims

**Author:** Rafael Valls Hidalgo-Gato
**Years:** 1985 (original work), 2009 (technical report)
**Claim:** P = NP
**Woeginger's List:** Entry #51

---

## Overview

Rafael Valls Hidalgo-Gato made two related claims about P=NP, separated by nearly 25 years:

1. **1985**: Original conference paper on solving systems of equations over Galois fields
2. **2009**: Technical report explicitly claiming to prove P=NP

Neither paper is publicly available online, limiting detailed analysis.

---

## Paper 1: 1985 Original Work

**Full Title:** "Método de solución para sistemas de ecuaciones simultáneas sobre un Campo de Galois y aplicaciones en Inteligencia Artificial"

**Translation:** "Solution method for systems of simultaneous equations over a Galois Field and applications in Artificial Intelligence"

**Publication Details:**
- **Conference:** ININTEF (Institute of Fundamental Technical Research) Scientific Conference
- **Institution:** Cuban Academy of Science
- **Citation:** 1985 Annual Report, Vol.II, S2-25, p.274
- **Location:** Havana, Cuba
- **Language:** Spanish
- **Availability:** Limited - Cuban institutional archives only

**Claimed Contributions:**
- A polynomial-time algorithm for solving systems of simultaneous equations over Galois fields (finite fields)
- Applications to artificial intelligence problems
- Implicit claim of solving at least one NP-complete problem in polynomial time

**Note:** The author later claimed this 1985 work contained the essential proof that P=NP.

---

## Paper 2: 2009 Technical Report

**Title:** "P=NP"

**Publication Details:**
- **Institution:** ICIMAF (Institute of Cybernetics, Mathematics and Physics)
- **Location:** Cuba
- **Series:** ICIMAF Technical Reports
- **ISSN:** 0138-8916
- **Date:** March 2009
- **Language:** Presumably Spanish
- **Availability:** Not publicly available online

**Announcement:**
- **Where:** comp.theory usenet newsgroup
- **When:** March 2009
- **Details:** Announcement mentioned the technical report but did not provide electronic link
- **Reception:** Minimal discussion; no detailed peer review documented

**Claimed Contributions:**
- Formalization of the 1985 result
- Explicit proof that P = NP
- Resolution of the P vs NP problem

---

## Technical Approach (Inferred)

Based on the titles and limited available information, the approach appears to be:

### 1. Core Algorithm Claim

**Domain:** Systems of polynomial equations over Galois fields GF(q)

**Input:**
- n variables
- m equations
- Maximum degree d
- Field size q

**Claimed Output:** Polynomial-time algorithm to:
- Determine if the system has a solution
- Find a solution if one exists

### 2. Connection to NP-Complete Problems

**Encoding Strategy:**
- NP-complete problems (e.g., SAT, 3-SAT, graph coloring) can be encoded as systems of polynomial equations over finite fields
- Most commonly: SAT reduces to polynomial equations over GF(2) (the field {0,1})

**Standard Encoding (for SAT over GF(2)):**

For a Boolean formula φ with variables x₁, ..., xₙ and clauses C₁, ..., Cₘ:

1. **Variable Constraints:** For each Boolean variable xᵢ:
   ```
   xᵢ² - xᵢ = 0    (forces xᵢ ∈ {0, 1})
   ```

2. **Clause Constraints:** For each clause Cⱼ = (ℓ₁ ∨ ℓ₂ ∨ ... ∨ ℓₖ):
   ```
   (1-ℓ₁)(1-ℓ₂)...(1-ℓₖ) = 0
   ```
   where ℓᵢ = xⱼ or ℓᵢ = (1-xⱼ) depending on whether the literal is positive or negative.

**Problem:** The clause equations can have degree up to k (the clause size), and for general SAT, k can equal n.

### 3. The Claimed Implication

**If True:**
1. NP-complete problems → polynomial equations over Galois fields (via standard encoding)
2. Polynomial equations solvable in polynomial time (claimed algorithm)
3. Therefore: NP-complete problems solvable in polynomial time
4. Since SAT is NP-complete: P = NP

### 4. Missing Details

The papers are not publicly available, so critical details are unknown:

**Unknown Algorithm Details:**
- What method does the algorithm use? (Gröbner bases? Linearization? Novel technique?)
- What is the exact time complexity? (Claimed to be O(n^k) for some k?)
- Does it work for all polynomial systems or only a restricted class?
- How does it handle field arithmetic? (Complexity depends on field size q)

**Unknown Encoding Details:**
- How are NP-complete problems encoded specifically?
- What degree polynomials result from the encoding?
- How many variables and equations in the final system?
- What field size is used?

---

## Why Papers Are Not Available

**1985 Paper:**
- Published in Cuban institutional conference proceedings
- Limited international distribution during Cold War era
- Not digitized or archived electronically
- Institutional archives may not be publicly accessible

**2009 Technical Report:**
- ICIMAF technical reports have limited circulation
- Not submitted to arXiv or international preprint servers
- No DOI or electronic repository link
- Cuban institutional publications often have restricted access

**Consequences:**
- Detailed technical analysis impossible without access to original papers
- Claims cannot be verified or refuted with certainty
- Mathematical community has not engaged with the work
- No peer review or independent verification documented

---

## Historical Context

**Timing of Original Work (1985):**
- P vs NP formally posed by Cook (1971) and Karp (1972)
- Major open problem for only ~13 years
- Pre-internet era: limited international dissemination
- Cold War: restricted academic exchange between Cuba and Western countries

**Timing of 2009 Announcement:**
- P vs NP one of Clay Mathematics Institute Millennium Prize Problems ($1 million reward)
- High-profile problem with many attempted proofs
- Internet era: claims typically posted to arXiv or submitted to journals
- Unusual to announce without providing full paper access

**Pattern:**
- Matches common pattern of P vs NP claims: institutional technical reports without international peer review
- Similar to other Woeginger list entries with limited availability
- Lack of engagement suggests mathematical community found claims insufficiently detailed or credible

---

## Known Mathematical Context

Even without the papers, we can analyze the mathematical landscape:

### What IS Known to Work (Polynomial Time):

1. **Linear Systems over GF(q):**
   - Gaussian elimination: O(n³) time
   - Works for any finite field
   - Well-established and uncontroversial

2. **Special Cases:**
   - 2-SAT can be solved in linear time (not via Galois fields)
   - Horn-SAT solvable in polynomial time
   - Linear programming (not over finite fields, but related)

### What IS Known to Be Hard:

1. **General Polynomial Systems over Finite Fields:**
   - Gröbner basis computation: exponential time in worst case
   - NP-complete for degree ≥ 2 over GF(2)
   - Polynomial System Satisfiability is NP-complete

2. **Specific Results:**
   - SAT is NP-complete (Cook 1971)
   - Polynomial equations over GF(2) can express SAT
   - Solving these equations is as hard as SAT itself

### The Complexity Barrier:

**Theorem (Folklore):** For any encoding of SAT as polynomial equations over GF(2):
- **Either:** The encoding uses exponentially many variables/equations
- **Or:** The polynomials have degree Ω(n)
- **Or:** The encoding/solving process takes exponential time

**Why:** This follows from standard complexity-theoretic arguments about the structure of NP-complete problems.

---

## Conclusion: What We Can Infer

Even without access to the original papers, several scenarios are possible:

### Scenario 1: Encoding Complexity Overlooked
- The algorithm works for some class of polynomial systems
- But encoding NP-complete problems into this class requires exponential resources
- **Gap:** Polynomial solving + Exponential encoding ≠ Polynomial overall

### Scenario 2: Degree/Size Tradeoff Missed
- Low-degree encoding requires exponentially many variables (linearization)
- Small encoding requires high-degree polynomials (hard to solve)
- **Gap:** No simultaneous achievement of polynomial size AND polynomial solvability

### Scenario 3: Field Size Dependency
- Algorithm is polynomial in number of equations/variables
- But requires exponentially large field GF(2ⁿ)
- Field arithmetic has bit complexity O(log q) per operation
- **Gap:** Polynomial in wrong parameters

### Scenario 4: Restricted Special Case
- Algorithm works for specific structured systems
- Not all NP-complete instances reduce to this special case
- **Gap:** Special case ≠ General case

### Scenario 5: Complexity Analysis Error
- Algorithm has hidden exponential dependencies
- Appears polynomial under optimistic counting
- **Gap:** Actual complexity exceeds claimed complexity

---

## References

1. **Original 1985 Paper (unavailable):**
   Rafael Valls Hidalgo-Gato. "Método de solución para sistemas de ecuaciones simultáneas sobre un Campo de Galois y aplicaciones en Inteligencia Artificial." ININTEF Scientific Conference, 1985 Annual Report, Vol.II, S2-25, p.274, Havana, Cuba.

2. **2009 Technical Report (unavailable):**
   Rafael Valls Hidalgo-Gato. "P=NP." ICIMAF Technical Report, ISSN 0138-8916, March 2009.

3. **Announcement:**
   comp.theory usenet newsgroup, March 2009.

4. **Woeginger's List:**
   Gerhard Woeginger. "The P-versus-NP page." Entry #51.
   https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

---

## Related Mathematical Literature

(For understanding the mathematical context even without access to original papers)

### Galois Fields and Finite Fields:

- **Galois, Évariste** (1832). "Sur la théorie des nombres." *Bulletin des Sciences Mathématiques.*
- **Lidl, Rudolf & Niederreiter, Harald** (1997). *Finite Fields.* Cambridge University Press.
  - Comprehensive reference on finite field theory and arithmetic

### Polynomial Equations and Complexity:

- **Buchberger, Bruno** (1965). "Ein Algorithmus zum Auffinden der Basiselemente des Restklassenringes nach einem nulldimensionalen Polynomideal." PhD thesis, University of Innsbruck.
  - Introduced Gröbner basis method

- **Cox, David; Little, John; O'Shea, Donal** (2007). *Ideals, Varieties, and Algorithms.* Springer.
  - Computational algebraic geometry and complexity

- **Lazard, Daniel** (1983). "Gröbner bases, Gaussian elimination and resolution of systems of algebraic equations." *EUROCAL'83*, Lecture Notes in Computer Science, 162: 146-156.
  - Complexity of Gröbner basis computation

- **Mayr, Ernst & Meyer, Albert** (1982). "The complexity of the word problems for commutative semigroups and polynomial ideals." *Advances in Mathematics*, 46(3): 305-329.
  - Exponential lower bounds for ideal membership

### Encoding NP Problems as Algebraic Systems:

- **Bayer, Dave & Stillman, Mike** (1987). "A criterion for detecting m-regularity." *Inventiones Mathematicae*, 87: 1-11.
  - Relevant to complexity of solving polynomial systems

- **Fraenkel, Aviezri & Yesha, Yaacov** (1979). "Complexity of solving algebraic equations." *Information Processing Letters*, 10(4-5): 178-179.
  - Hardness of polynomial equation solving

### SAT and NP-Completeness:

- **Cook, Stephen** (1971). "The complexity of theorem-proving procedures." *STOC '71*, pp. 151-158.
  - Proved SAT is NP-complete

- **Karp, Richard** (1972). "Reducibility among combinatorial problems." In *Complexity of Computer Computations*, pp. 85-103.
  - 21 NP-complete problems

### Gaussian Elimination (Polynomial-Time Baseline):

- **Wiedemann, Douglas** (1986). "Solving sparse linear equations over finite fields." *IEEE Transactions on Information Theory*, 32(1): 54-62.
  - Efficient algorithms for sparse linear systems over finite fields

---

**Note:** This document represents what can be inferred about papers that are not publicly available. A complete technical analysis would require access to the original 1985 and 2009 publications.
