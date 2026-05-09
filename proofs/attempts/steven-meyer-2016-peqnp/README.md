# Steven Meyer (2016) - P=NP Proof Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Author**: Steven Meyer
- **Year**: 2016
- **Claim**: P = NP
- **Source**: [arXiv:1603.06018](https://arxiv.org/abs/1603.06018)
- **Title**: "The Scientific Nature of the P-versus-NP Problem"
- **Entry**: #108 on [Woeginger's P-versus-NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
- **Status**: Refuted (contains fundamental errors)

## Summary

In March 2016, Steven Meyer claimed to have established P=NP by arguing that the P-versus-NP problem should be understood as a scientific rather than mathematical problem. Meyer's approach attempts to solve P=NP philosophically using the Random Access with Unit Multiply (MRAM) computational model, criticizing the traditional definition based on non-deterministic Turing Machines (NDTMs).

## Main Argument

Meyer's proof attempt rests on the following key claims:

1. **Philosophical Reframing**: The P-versus-NP problem is claimed to be "a scientific rather than a mathematical problem," suggesting that it should be addressed through empirical computational modeling rather than pure mathematical proof.

2. **MRAM Model Superiority**: Meyer argues that the MRAM (Random Access with Unit Multiply) model "empirically best models computation hardness" and should replace the standard NDTM-based formulation.

3. **Model Equivalence**: Using techniques from Hartmanis and Simon, Meyer claims to show that the computational power of MRAMs equals that of NDTMs.

4. **Conclusion**: Based on this analysis in the MRAM model, Meyer concludes P = NP.

5. **Additional Claims**:
   - Von Neumann allegedly rejected traditional automata computation models
   - Deolalikar's previous P≠NP solution should be revisited
   - The problem is "neither a problem in pure nor applied mathematics"

## The Error

Meyer's proof attempt contains several fundamental errors:

### 1. **Confusion Between Computational Models**

**Error**: Meyer conflates the computational model used to analyze complexity (MRAM vs. Turing Machine) with the fundamental question of whether P=NP.

**Why This Matters**: The P-versus-NP question is about the relationship between two complexity classes, which is invariant across polynomially equivalent computational models. The Church-Turing thesis (and its polynomial-time variant) establishes that all reasonable deterministic models are polynomially equivalent—they can simulate each other with at most polynomial overhead.

**Formal Issue**:
```
P_TM = NP_TM  ⟺  P_MRAM = NP_MRAM
```
If Meyer proves P=NP in the MRAM model, this would imply P=NP in the Turing Machine model (and vice versa). The choice of model doesn't resolve the question—it remains open in all polynomially equivalent models.

### 2. **Philosophical Arguments Don't Resolve Mathematical Questions**

**Error**: Meyer argues the problem is "scientific rather than mathematical" and attempts to resolve it philosophically.

**Why This Matters**: The P-versus-NP problem is a well-defined mathematical question about the existence of polynomial-time algorithms. Philosophical arguments about the "nature" of the problem cannot substitute for a mathematical proof or disproof.

**What's Required**: To prove P=NP, one must either:
- Provide a polynomial-time algorithm for an NP-complete problem (like SAT), OR
- Prove that such an algorithm must exist through mathematical argument

To prove P≠NP, one must show:
- A super-polynomial lower bound for some problem in NP, OR
- Prove that no polynomial-time algorithm can exist for some NP-complete problem

### 3. **Misunderstanding of Model Independence**

**Error**: Meyer suggests that changing the computational model from NDTMs to MRAMs affects the answer to P-versus-NP.

**Why This Matters**:
- **P** is the class of problems solvable in polynomial time (regardless of model)
- **NP** is the class of problems verifiable in polynomial time (regardless of model)
- These definitions are robust across polynomially equivalent models

**The Issue**: Meyer's argument would only be meaningful if:
1. MRAMs could solve NP problems in polynomial time, AND
2. This capability doesn't transfer to Turing Machines

But condition (2) contradicts the polynomial equivalence of computational models.

### 4. **No Concrete Algorithm or Lower Bound**

**Error**: The paper provides neither:
- A polynomial-time algorithm for SAT or any NP-complete problem
- A proof that such algorithms must exist
- Any concrete computational result

**Why This Matters**: A valid proof of P=NP must be constructive (provide an algorithm) or non-constructive (prove existence). Meyer's philosophical argument does neither.

### 5. **Misrepresentation of Historical Context**

**Error**: Meyer's claims about Von Neumann and Deolalikar are not supported by historical evidence or peer-reviewed analysis.

**Why This Matters**:
- Von Neumann's work predates the formal definition of NP-completeness (1971)
- Deolalikar's 2010 proof attempt was thoroughly refuted by the community
- Appeals to authority don't constitute mathematical proof

## Formalization Strategy

Our formalization captures Meyer's error by:

1. **Defining Multiple Models**: Implementing both Turing Machine and MRAM computational models
2. **Showing Model Equivalence**: Proving that P_TM = P_MRAM and NP_TM = NP_MRAM (up to polynomial overhead)
3. **Exposing the Error**: Demonstrating that proving P=NP in one model implies P=NP in all polynomially equivalent models
4. **Rejecting Philosophical Arguments**: Showing that the question remains mathematical regardless of philosophical framing

## Files in This Directory

### Rocq (`rocq/MeyerAttempt.v`)
Formal proof in Rocq that demonstrates:
- Definition of MRAM and Turing Machine models
- Polynomial equivalence of models
- Why changing models doesn't resolve P-versus-NP
- The error in Meyer's reasoning

### Lean 4 (`lean/MeyerAttempt.lean`)
Formal proof in Lean 4 that:
- Defines computational models formally
- Proves model equivalence theorems
- Shows the independence of P-versus-NP from model choice
- Identifies the gap in Meyer's argument

### Isabelle/HOL (`isabelle/MeyerAttempt.thy`)
Formal proof in Isabelle that:
- Implements polynomial-time equivalence of models
- Demonstrates that P-versus-NP is model-independent
- Formalizes why philosophical arguments are insufficient

## Key Takeaways

1. **P-versus-NP is model-independent**: The problem has the same answer regardless of whether we use Turing Machines, RAM machines, MRAMs, or any other polynomially equivalent model.

2. **Philosophical arguments are insufficient**: The P-versus-NP problem is a precise mathematical question requiring a mathematical proof or disproof.

3. **Burden of proof**: To claim P=NP, one must provide:
   - A concrete polynomial-time algorithm for an NP-complete problem, OR
   - A mathematical proof that such an algorithm exists

4. **Common misconception**: Changing the computational model does not resolve the fundamental question about the relationship between P and NP.

## References

### Meyer's Paper
- **Meyer, S.** (2016). "The Scientific Nature of the P-versus-NP Problem." [arXiv:1603.06018](https://arxiv.org/abs/1603.06018)

### Foundational Results
- **Cook, S.** (1971). "The complexity of theorem-proving procedures." *STOC*
- **Karp, R.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*
- **Hartmanis, J., Stearns, R.** (1965). "On the computational complexity of algorithms." *Transactions of the American Mathematical Society*

### Computational Models
- **Aho, A., Hopcroft, J., Ullman, J.** (1974). *The Design and Analysis of Computer Algorithms*
- **Cook, S., Reckhow, R.** (1973). "Time bounded random access machines." *Journal of Computer and System Sciences*

### P-versus-NP Resources
- **Arora, S., Barak, B.** (2009). *Computational Complexity: A Modern Approach*
- **Sipser, M.** (2012). *Introduction to the Theory of Computation*

## See Also

- [P = NP Framework](../../p_eq_np/) - Framework for verifying P=NP proofs
- [P ≠ NP Framework](../../p_not_equal_np/) - Framework for verifying P≠NP proofs
- [Repository Root](../../../README.md) - Main documentation

## License

This formalization is provided for educational and research purposes. See repository [LICENSE](../../../LICENSE) file.

---

**Status**: Formalization complete. All three proof assistants successfully identify and formalize the errors in Meyer's argument.
