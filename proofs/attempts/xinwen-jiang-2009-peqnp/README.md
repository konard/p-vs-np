# Xinwen Jiang (2009) - P=NP via Polynomial Time Algorithm for Hamiltonian Circuit

**Attempt ID**: 53 (from Woeginger's list)
**Author**: Xinwen Jiang
**Year**: 2009 (with subsequent versions in 2010, 2011, and 2013)
**Claim**: P = NP
**Status**: Not accepted by the research community

## Summary

In 2009, Xinwen Jiang proposed a polynomial-time algorithm for the Hamiltonian Circuit problem, claiming this would prove P = NP. The approach introduces an intermediate problem called the "Multistage Graph Simple Path (MSP)" problem and attempts to show that:
1. The Hamiltonian Circuit (HC) problem can be polynomially reduced to the MSP problem
2. The MSP problem can be solved in polynomial time

Since Hamiltonian Circuit is NP-complete, solving it in polynomial time would indeed prove P = NP.

## Directory Structure

- `original/` - Original paper description and reconstruction
  - `README.md` - Description of the proof idea and detailed error analysis
  - `ORIGINAL.md` - Reconstruction of the original paper content in English
- `proof/` - Forward proof formalization (Jiang's claimed argument)
  - `README.md` - Explanation of what the formalizations capture
  - `lean/JiangProof.lean` - Lean 4 formalization
  - `rocq/JiangProof.v` - Rocq (Coq) formalization
- `refutation/` - Refutation of Jiang's argument
  - `README.md` - Explanation of why the proof fails
  - `lean/JiangRefutation.lean` - Lean 4 refutation
  - `rocq/JiangRefutation.v` - Rocq refutation

## Core Errors

Four critical errors are identified and formalized:

### 1. Vague Problem Definition
The MSP problem formulation is poorly defined with unclear notation and missing formal definitions. Without a precise problem definition, it is impossible to verify whether the reduction is correct.

### 2. Possible Wrong Problem Class
The MSP problem may actually be a polynomial-time solvable problem rather than an NP-complete one. If MSP ∈ P, then reducing HC to MSP does not help solve HC.

> "Jiang's labelled multistage graphs correspond to partially ordered sets, and finding Hamiltonian cycles in their comparability graphs is known not to be NP-complete."
> — Hacker News discussion

### 3. Lack of Rigorous Proof
The paper lacks rigorous proofs for algorithm correctness and relies on experimental validation instead.

### 4. Experimental Validation ≠ Mathematical Proof
> "The MSP problem possesses a novel polynomial-time heuristic algorithm, which has undergone extensive test and always give the correct answer for all instances (more than 5 × 10^7) generated up to now. Although there is no broad consensus with proving the correctness of the polynomial-time heuristic algorithm for the MSP problem."

Testing millions of instances is not sufficient to prove an algorithm always works.

## References

- **Primary Source**: [arXiv:1305.5976](https://arxiv.org/abs/1305.5976) - "A Polynomial Time Algorithm for the Hamilton Circuit Problem"
- **Technical Analysis**: [Hacker News Discussion](https://news.ycombinator.com/item?id=5785693)
- **Catalog**: [Woeginger's P vs NP List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) - Entry #53
