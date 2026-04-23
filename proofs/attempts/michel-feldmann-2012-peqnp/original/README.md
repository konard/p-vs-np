# Original Paper: Solving Satisfiability by Bayesian Inference

**Author:** Michel Feldmann
**Year:** 2012 (original), 2020 (revised, v5)
**arXiv ID:** [1205.6658v5](https://arxiv.org/abs/1205.6658)
**Claim:** P = NP

---

## Abstract

The paper proposes a polynomial-time decision procedure for Boolean satisfiability (3-SAT) using Bayesian inference. The approach encodes Boolean variables as probability distributions in a Kolmogorov probability space, converts the SAT problem into a linear programming (LP) system, and claims that checking LP feasibility decides satisfiability in polynomial time.

---

## Files

- `ORIGINAL.pdf` - Original paper (arXiv:1205.6658)
- `ORIGINAL.md` - Markdown conversion of the original paper text

---

## Summary of the Proof Idea

Feldmann's approach proceeds in four steps:

1. **Probabilistic Encoding**: Assign to each Boolean variable X_i a conditional probability P(i) = P(X_i = 1 | Λ) in a Kolmogorov probability space.

2. **LP Construction**: For each clause in the SAT formula, generate "specific equations" relating the probabilities. Add "consistency equations" to enforce probability axioms. Together, these form an LP system.

3. **Equivalence Claim**: For "strict satisfiability" problems, claims that LP feasibility is equivalent to Boolean satisfiability.

4. **Polynomial-Time Conclusion**: Since LP feasibility can be checked in polynomial time (Khachiyan 1979, Karmarkar 1984), concludes that 3-SAT ∈ P, and therefore P = NP.

---

## References

- Cook, S. (1971). "The complexity of theorem proving procedures." STOC 1971.
- Karp, R. (1972). "Reducibility among combinatorial problems."
- Khachiyan, L. (1979). "A polynomial algorithm in linear programming."
- Karmarkar, N. (1984). "A new polynomial-time algorithm for linear programming."
- Woeginger's List: Entry #90 - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
