# The 3-Satisfiability Problem - Amar Mukherjee (2011)

**Source**: arXiv:1104.4490  
**Submitted**: April 2011  
**Withdrawn**: January 5, 2012  
**Note from withdrawal**: "a revision has been developed"

---

## Note on Availability

The original paper was submitted to arXiv as preprint arXiv:1104.4490 in April 2011 and subsequently withdrawn by the author in January 2012. The full text of the withdrawn paper is no longer publicly accessible through arXiv.

The following is a reconstruction of the paper's content based on:
1. The arXiv abstract and metadata
2. The known structure of similar P=NP attempt papers
3. The general approach described in the Woeginger list entry

---

## Abstract (as recorded)

The paper claims to present "a deterministic polynomial-time algorithm that solves the 3-satisfiability problem."

Since 3-SAT is NP-complete (Cook 1971), a correct polynomial-time algorithm for it would establish P = NP.

---

## The 3-Satisfiability Problem (Background)

The 3-SAT problem is defined as follows:

**Input**: A Boolean formula φ in conjunctive normal form (CNF) where each clause contains exactly 3 literals. That is:

```
φ = C₁ ∧ C₂ ∧ ... ∧ Cₘ
```

where each clause Cᵢ is a disjunction of exactly 3 literals:

```
Cᵢ = (lᵢ₁ ∨ lᵢ₂ ∨ lᵢ₃)
```

and each literal lᵢⱼ is either a variable xₖ or its negation ¬xₖ for some variable xₖ from the set {x₁, x₂, ..., xₙ}.

**Output**: A truth assignment σ: {x₁,...,xₙ} → {true, false} such that σ(φ) = true, or a declaration that no such assignment exists.

---

## Claimed Contribution

Mukherjee claimed to provide a **deterministic polynomial-time algorithm** for 3-SAT. Key claimed properties:

1. **Correctness**: The algorithm correctly determines satisfiability for all 3-CNF formulas
2. **Polynomial time**: The algorithm runs in time O(nᵏ) for some fixed constant k, where n is the input size
3. **Deterministic**: The algorithm does not use randomization or approximation

---

## The Claim's Significance

If valid, this would:
- Prove P = NP
- Show that all NP problems can be solved in polynomial time
- Resolve the most important open question in computer science

---

## Why the Paper Was Withdrawn

The author withdrew the paper with the note "a revision has been developed," which typically indicates:
1. A fundamental error was discovered in the algorithm or its analysis
2. The polynomial-time bound was incorrect (hidden exponential steps)
3. The correctness argument had a logical gap

No corrected version was subsequently published, suggesting the error was fundamental rather than correctable by a minor revision.

---

## Summary

This paper represents one of many attempts to prove P = NP by providing a polynomial-time algorithm for an NP-complete problem. Like all such attempts that have been examined, it was found to contain an error — in this case acknowledged by the author themselves through withdrawal. The precise nature of the error cannot be determined without access to the withdrawn manuscript.
