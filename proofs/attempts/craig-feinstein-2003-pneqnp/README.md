# Craig Alan Feinstein (2003-04) - P≠NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #11](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 11 (from Woeginger's list)
- **Author**: Craig Alan Feinstein
- **Year**: 2003-04
- **Claim**: P ≠ NP
- **Paper Titles**:
  - "Evidence that P is not equal to NP" (2003)
  - "P is not equal to NP" (withdrawn after counterexample discovered)
- **Status**: Withdrawn by author
- **Source**: arXiv (2003-04 submissions)

---

## Summary

Craig Alan Feinstein's 2003-04 attempt(s) claimed to prove that P ≠ NP by working within a "restricted model of computation." The initial paper, "Evidence that P is not equal to NP," was careful to note that it provided evidence rather than a complete proof within this restricted computational model.

A subsequent paper titled "P is not equal to NP" made a stronger claim but was **withdrawn by the author after a counterexample was discovered**, demonstrating a fatal flaw in the reasoning.

This represents entry #11 on Woeginger's comprehensive list of P vs NP attempts. The work is notable as an early example (2003-04) of an attempt that:
1. Explicitly acknowledged working in a restricted model
2. Was formally withdrawn after peer review and scrutiny revealed errors

---

## The Main Argument

### Restricted Computational Model

Feinstein's approach involved:
1. Defining a specific restricted model of computation
2. Attempting to show that within this model, NP-complete problems require super-polynomial time
3. Arguing that results in the restricted model transfer to general computation

### The Core Strategy

The argument appears to have followed this pattern:
1. **Model Definition**: Establish a computational model with certain restrictions or characteristics
2. **Lower Bound in Model**: Prove that NP-complete problems require exponential (or at least super-polynomial) time in this model
3. **Generalization Claim**: Assert that the lower bound in the restricted model implies P ≠ NP in general

This strategy is similar to other attempts that work with restricted models, including:
- Circuit complexity lower bounds
- Decision tree lower bounds
- Communication complexity arguments

---

## The Error

### The Fatal Counterexample

According to Woeginger's list, Feinstein's stronger claim in "P is not equal to NP" was **withdrawn after a counterexample was discovered**. While the specific details of the counterexample are not publicly documented in the available sources, this indicates that:

1. The proof contained a logical flaw or gap
2. The flaw was significant enough to invalidate the main claim
3. The author responsibly withdrew the paper upon discovering the error

### Common Pitfalls in Restricted Model Approaches

Based on the pattern of similar attempts, likely errors include:

#### 1. **Invalid Transfer from Restricted to General Models**

**The Problem**: Lower bounds in restricted models don't automatically imply lower bounds in unrestricted computation.

**Why it fails**:
- A restricted model may forbid certain algorithmic strategies that are available in general computation
- Proving that no algorithm *of type X* can solve a problem in polynomial time doesn't prove that *no algorithm at all* can do so

**Example**: Proving that comparison-based sorting requires Ω(n log n) comparisons doesn't prove that sorting requires Ω(n log n) time in general (radix sort exists).

#### 2. **Circular Reasoning or Unproven Assumptions**

**The Problem**: The proof may assume what it's trying to prove, or rely on unproven lower bound assumptions.

**Common form**:
- Assume that certain operations are "necessary" for solving NP-complete problems
- Show that these operations require super-polynomial time in the restricted model
- Conclude P ≠ NP

**The gap**: The assumption that these operations are necessary is often equivalent to assuming P ≠ NP.

#### 3. **Confusion Between Necessary and Sufficient Conditions**

**The Problem**: Showing that a particular algorithmic approach requires exponential time doesn't prove that all approaches do.

**Analogy**: Proving that walking from New York to Los Angeles takes months doesn't prove that the journey requires months (planes exist).

#### 4. **Model-Specific Artifacts**

**The Problem**: The lower bound may rely on specific limitations of the model that don't reflect fundamental computational barriers.

**Example**: A model that charges exponentially for certain operations might make polynomial-time algorithms appear exponential due to the charging scheme, not due to inherent problem difficulty.

---

## The Critical Gap

For any restricted model approach to prove P ≠ NP, it must show:

1. **Model Definition**: The restricted model is well-defined and captures essential aspects of general computation
2. **Lower Bound**: NP-complete problems require super-polynomial time in the model (proven rigorously)
3. **Transfer Principle**: Lower bounds in the restricted model imply lower bounds in general (proven rigorously)

Step 3 is where most restricted model approaches fail. The counterexample found in Feinstein's work likely exploited a flaw in one of these three steps, most probably step 2 or 3.

---

## Related Work and Context

### Similar Approaches That Also Failed

Feinstein's approach is part of a broader pattern of attempts using restricted models:

1. **Decision Tree Lower Bounds**: While we have exponential lower bounds for some NP-complete problems in decision tree models, these don't transfer to general computation because decision trees are highly restricted.

2. **Circuit Complexity**: We have some lower bounds for restricted circuit classes, but proving super-polynomial lower bounds for general circuits remains open (and would prove P ≠ NP).

3. **Communication Complexity**: Lower bounds in communication complexity don't directly imply computational complexity lower bounds.

### Why Restricted Models Are Studied

Despite these attempts' failures, restricted models are valuable for:
- Understanding specific algorithmic techniques
- Proving conditional lower bounds
- Developing intuition about problem difficulty
- Making progress on related problems

However, proving P ≠ NP requires working with unrestricted models or finding a transfer principle that has eluded researchers for decades.

---

## Feinstein's Other Work (Context)

Around the same time period (2003-04), Feinstein published several papers making strong claims about unprovability:

1. **"The Riemann Hypothesis is Unprovable"** (arXiv:math/0309367, Sept 2003)
   - Claims a "simple proof" that the Riemann Hypothesis cannot be proven in any reasonable axiom system

2. **"The Collatz 3n+1 Conjecture is Unprovable"** (arXiv:math/0312309, Dec 2003)
   - Argues that any proof must have infinitely many lines

These papers share a common pattern with the P vs NP attempt:
- Making strong claims about fundamental open problems
- Relying on arguments about computational complexity or proof length
- Using reasoning that, under scrutiny, contains gaps or invalid transfer arguments

Later work by Feinstein (2005-06) on P vs NP used different approaches (see the separate formalization of his 2005 attempt using the "Mabel-Mildred-Feinstein" model).

---

## Lessons Learned

This attempt illustrates several important principles:

1. **Intellectual Honesty**: Feinstein withdrew the stronger claim when a counterexample was found, demonstrating scientific integrity.

2. **Peer Review Works**: The counterexample was discovered through the review process, showing the value of public scrutiny.

3. **Restricted Models Have Limits**: Proving lower bounds in restricted models is valuable but insufficient for resolving P vs NP.

4. **Transfer Principles Are Hard**: The gap between restricted and general models remains a fundamental barrier in complexity theory.

---

## Formalization Goals

The formal proof attempts in this directory aim to:

1. **Reconstruct the Argument**: Since the papers were withdrawn and details are limited, we construct a representative "restricted model" argument that captures the likely approach.

2. **Formalize Common Errors**: Show the typical patterns of errors in restricted model approaches:
   - Invalid transfer from restricted to general models
   - Circular reasoning in defining "necessary" operations
   - Confusion between lower bounds for specific algorithmic families vs. all algorithms

3. **Demonstrate Counter-Reasoning**: Formalize how counterexamples can invalidate such arguments.

4. **Educational Value**: Make explicit why restricted model approaches face fundamental challenges in proving P ≠ NP.

---

## Files in This Directory

- **paper/**: References and links to archived versions of the original papers
- **lean/**: Lean formalization demonstrating the pattern of error in restricted model arguments
- **coq/**: Coq formalization demonstrating the pattern of error in restricted model arguments
- **isabelle/**: Isabelle/HOL formalization demonstrating the pattern of error in restricted model arguments
- **README.md**: This file

---

## References

1. Woeginger, G. J. "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #11)
2. Feinstein, C. A. (2003-04). "Evidence that P is not equal to NP" (arXiv, withdrawn)
3. Feinstein, C. A. (2003-04). "P is not equal to NP" (arXiv, withdrawn after counterexample)
4. Feinstein, C. A. (2003). "The Riemann Hypothesis is Unprovable". arXiv:math/0309367
5. Feinstein, C. A. (2003). "The Collatz 3n+1 Conjecture is Unprovable". arXiv:math/0312309

---

## Status

- ✅ Attempt documented and error pattern identified
- ✅ Directory structure created
- 🚧 Lean formalization in progress
- 🚧 Coq formalization in progress
- 🚧 Isabelle formalization in progress

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #434](https://github.com/konard/p-vs-np/issues/434) | [PR #496](https://github.com/konard/p-vs-np/pull/496)
