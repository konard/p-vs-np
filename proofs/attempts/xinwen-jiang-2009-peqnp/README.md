# Xinwen Jiang (2009) - P=NP via Polynomial Time Algorithm for Hamiltonian Circuit

**Attempt ID**: 53 (from Woeginger's list)
**Author**: Xinwen Jiang
**Year**: 2009 (with subsequent versions in 2010, 2011, and 2013)
**Claim**: P = NP
**Status**: Not accepted by the research community

## Summary

In 2009, Xinwen Jiang proposed a polynomial-time algorithm for the Hamiltonian Circuit problem, claiming this would prove P = NP. The approach introduces an intermediate problem called the "Multistage Graph Simple Path (MSP)" problem and attempts to show that (1) the Hamiltonian Circuit problem can be polynomially reduced to the MSP problem, and (2) the MSP problem can be solved in polynomial time. Since Hamiltonian Circuit is NP-complete, solving it in polynomial time would indeed prove P = NP.

## Main Argument

### The Approach

1. **Multistage Graph Definition**: Jiang defines a new problem formulation called the "Multistage Graph Simple Path (MSP)" problem
2. **Polynomial Reduction**: Shows that the Hamiltonian Circuit (HC) problem can be polynomially reduced to the MSP problem
3. **Polynomial Algorithm**: Claims to provide a polynomial-time algorithm for solving the MSP problem
4. **Claimed Implication**: If HC reduces to MSP in polynomial time, and MSP can be solved in polynomial time, then P = NP

### Key Technical Claims

The crucial claims were:
- The MSP problem is **both** NP-complete (due to the reduction from HC)
- AND the MSP problem has a polynomial-time algorithm
- These two facts together would prove P = NP

### Publication History

- **2007**: Earlier version published in Chinese journal
- **2009**: Initial claim made
- **2010, 2011**: Updated versions
- **May 2013**: Published on arXiv (arXiv:1305.5976)
- **Ongoing**: Author maintained a blog with additional details and experimental validation

## The Errors

### 1. Problem Definition Issues

**The Error**: The MSP problem formulation is poorly defined with unclear notation and missing formal definitions.

**Why This Matters**:
- Without a precise problem definition, it's impossible to verify whether the reduction is correct
- Undefined notation makes it difficult to evaluate the algorithm's correctness
- Multiple reviewers noted that "the problem could likely be formalized in a more effective way"

### 2. Possible Wrong Problem Class

**The Error**: The MSP problem may actually be a **polynomial-time solvable** problem rather than an NP-complete one.

**Critical Observation** (from Hacker News discussion):
> "Jiang's labelled multistage graphs correspond to partially ordered sets, and finding Hamiltonian cycles in their comparability graphs is known not to be NP-complete."

**Why This Matters**:
- If the MSP problem is actually in P (polynomial time), then reducing HC to MSP doesn't help solve HC
- You cannot solve an NP-complete problem by reducing it to an easier problem
- This would mean the "reduction" goes in the wrong direction or doesn't preserve hardness

### 3. Lack of Rigorous Proof

**The Error**: The paper lacks the mathematical rigor expected for such an extraordinary claim.

**Specific Issues**:
- Heavy reliance on self-citation (~10 references to author's own work)
- Almost no citation of contemporary research in complexity theory
- Does not use standard typesetting (TeX/LaTeX), cited as a red flag by Scott Aaronson's checklist for false mathematical breakthroughs
- The author himself showed uncertainty, stating on his website: "It seems our algorithm is a polynomial one"

**Why This Matters**:
- Extraordinary claims require extraordinary evidence
- A proof of P = NP would need to be exceptionally rigorous and clear
- The lack of engagement with existing complexity theory literature suggests the work may not properly address known barriers

### 4. Experimental Validation vs. Proof

**The Error**: The author relies on experimental validation rather than mathematical proof.

**From subsequent work** (2014):
> "The MSP problem possesses a novel polynomial-time heuristic algorithm, which has undergone extensive test and always give the correct answer for all instances (more than 5 × 10^7) generated up to now. Although there is no broad consensus with proving the correctness of the polynomial-time heuristic algorithm for the MSP problem."

**Why This Matters**:
- Testing many instances is not sufficient to prove an algorithm always works
- Many incorrect algorithms can appear to work on randomly generated test cases
- For P = NP, a rigorous mathematical proof is required, not experimental evidence

## Broader Context

### Why This Approach Is Tempting

The approach is appealing because:
- Hamiltonian Circuit is a well-known NP-complete problem
- If we could solve it in polynomial time, we would indeed prove P = NP
- Multistage graphs are a real concept in computer science (used for dynamic programming)
- The reduction approach is a valid strategy in complexity theory

### The Critical Distinction: Reduction Direction

- **Correct Approach**: To prove P = NP, reduce HC to a problem you can solve in polynomial time
- **Requirement**: The target problem must genuinely be solvable in polynomial time
- **The Trap**: The MSP problem may either:
  1. Not be well-defined enough to analyze
  2. Actually be NP-complete itself (in which case the algorithm is likely incorrect)
  3. Be in P but not equivalent to HC (in which case the reduction doesn't work)

### Lack of Peer Review Acceptance

**Critical Fact**: The paper appears only on arXiv, not in a peer-reviewed venue.

**Why This Matters**:
- ArXiv accepts papers without peer review
- The theoretical computer science community has not accepted this proof
- No major complexity theorists have validated the approach
- The ongoing revisions (2009, 2010, 2011, 2013) without peer-reviewed publication suggest fundamental issues

## Community Reception

### Hacker News Discussion (June 2013)

Key points from the discussion:

1. **Skepticism about formalization**: "The problem could likely be formalized in a more effective way"
2. **Potential misclassification**: Suggestion that the problem may be polynomial rather than NP-complete
3. **Poor presentation**: Multiple comments about unclear notation and lack of standard formatting
4. **Red flags**: References to Scott Aaronson's checklist for false mathematical proofs
5. **Lack of engagement**: Author has been working on this since 1993 without gaining traction in the academic community

### No Formal Refutation Published

Unlike some P vs NP attempts that have published counter-examples (e.g., Hofman's refutation of Diaby), this attempt lacks:
- A formal published refutation
- Acceptance in peer-reviewed literature
- Endorsement from the complexity theory community

The absence of acceptance is itself telling for such an extraordinary claim.

## Formalization Goals

In this directory, we formalize:

1. **The Basic Claim**: What a polynomial-time algorithm for Hamiltonian Circuit would mean
2. **The MSP Reduction Approach**: The structure of the argument via an intermediate problem
3. **Why This Would Imply P = NP**: If the reduction and algorithm were correct
4. **The Gaps**: Where the proof fails (problem definition, algorithm correctness, or reduction validity)

The formalization demonstrates that:
- The claim structure is reasonable (reduce to intermediate problem, solve it efficiently)
- The critical steps (well-defined MSP, correct reduction, polynomial algorithm) are non-trivial
- Without rigorous proofs of these steps, the argument fails
- Experimental validation cannot replace mathematical proof

## References

### Primary Sources

- **ArXiv Version**: Jiang, X. (2013). "A Polynomial Time Algorithm for the Hamilton Circuit Problem"
  - arXiv:1305.5976
  - Available at: https://arxiv.org/abs/1305.5976
- **Chinese Journal**: Earlier version published in 2007
- **Author's Blog**: trytoprovenpvsp.blog.sohu.com (historical)

### Analysis and Discussion

- **Hacker News Discussion** (June 2, 2013): "P might be NP: A Polynomial Time Algorithm for the Hamilton Circuit Problem"
  - https://news.ycombinator.com/item?id=5785693
  - Contains critical analysis and identification of potential errors
- **Scott Aaronson's Checklist**: Red flags for false mathematical breakthroughs
  - Referenced in community discussions about this paper

### Context

- **Woeginger's List**: Entry #53
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Hamiltonian Circuit Problem**: Known NP-complete problem
  - Part of Karp's 21 NP-complete problems (1972)

## Key Lessons

1. **Problem Definition is Critical**: A vague problem definition makes it impossible to verify a proof
2. **Reduction Direction Matters**: You must reduce from hard problems to easier ones, not the reverse
3. **Experimental Evidence ≠ Proof**: Testing millions of instances doesn't prove an algorithm is correct
4. **Peer Review is Essential**: Extraordinary claims require validation by the broader scientific community
5. **Presentation Matters**: Clear, rigorous mathematical exposition is necessary for complex proofs
6. **Self-Consistency Check**: If a problem is both "NP-complete" and "solvable in polynomial time," one of those claims is likely wrong (unless P = NP, which requires proof)
7. **Long-Term Persistence Without Acceptance**: If a proof remains unaccepted for many years despite revisions (1993-2013+), there are likely fundamental issues

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Hamiltonian Circuit Problem](../../problems/hamiltonian_circuit/) - The NP-complete problem at the heart of this attempt
- [Proof Experiments](../../experiments/) - Other experimental approaches to P vs NP
- [Repository README](../../../README.md) - Overview of the P vs NP problem
