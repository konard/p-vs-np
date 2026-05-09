# Original Paper Description: Xinwen Jiang (2009) - P=NP via Hamiltonian Circuit

**Author**: Xinwen Jiang
**Year**: 2009 (with subsequent versions in 2010, 2011, and 2013)
**Claim**: P = NP
**arXiv**: [arXiv:1305.5976](https://arxiv.org/abs/1305.5976)
**Woeginger's List**: Entry #53

## Core Idea

Xinwen Jiang attempts to prove P = NP by providing a polynomial-time algorithm for the **Hamiltonian Circuit (HC) problem**, which is known to be NP-complete.

The approach uses an intermediate problem called the **Multistage Graph Simple Path (MSP)** problem:

1. Define the MSP problem on multistage graphs
2. Show a polynomial-time reduction from HC to MSP
3. Provide a polynomial-time algorithm for MSP
4. Conclude: since HC (NP-complete) reduces to MSP, and MSP has a polynomial algorithm, P = NP

## How It Intended to Solve P vs NP

### The Argument Structure

If the following two claims hold simultaneously:
- **Reduction**: HC ≤_p MSP (Hamiltonian Circuit polynomially reduces to MSP)
- **Algorithm**: MSP ∈ P (MSP can be solved in polynomial time)

Then HC ∈ P, and since HC is NP-complete, P = NP.

### The Multistage Graph Construction

Given a graph G for which we want to decide if a Hamiltonian circuit exists:

1. **Construct a multistage graph** where:
   - Stages correspond to positions in a potential Hamiltonian path
   - Nodes at each stage represent vertices of the original graph
   - Edges between stages represent valid transitions

2. **Claim**: Finding a Hamiltonian circuit in G corresponds to finding a simple path through all stages of the multistage graph (the MSP problem)

3. **Polynomial Algorithm**: Jiang claims a dynamic-programming-like algorithm on the multistage structure can find such a path in polynomial time

### Publication History

- **~1993**: Author reportedly began working on the problem
- **2007**: Earlier version published in Chinese journal
- **2009**: Initial international claim
- **2010, 2011**: Updated versions
- **May 2013**: Published on arXiv (arXiv:1305.5976)
- **Ongoing**: Author maintained a blog (trytoprovenpvsp.blog.sohu.com) with additional details and experimental validation claiming >50 million test cases passed

## Detailed Error Explanation

### Error 1: Vague and Poorly Defined MSP Problem

The central problem: Jiang's MSP problem formulation lacks mathematical rigor.

- **Undefined notation**: Several symbols and operations are introduced without formal definition
- **Missing formalization**: The problem's input/output specification is imprecise
- **Unclear equivalence**: The claimed equivalence between HC instances and MSP instances is never rigorously established

As noted in Hacker News discussion: *"the problem could likely be formalized in a more effective way"* — meaning the definition is not precise enough to reason about.

### Error 2: Possible Misclassification (MSP May Be in P, Not NP-Complete)

A critical observation from technical reviewers:

> "Jiang's labelled multistage graphs correspond to partially ordered sets, and finding Hamiltonian cycles in their comparability graphs is known not to be NP-complete."

If the MSP problem is actually **polynomial-time solvable** (i.e., MSP ∈ P), then:
- The reduction HC ≤_p MSP proves nothing useful about the hardness of MSP
- Reducing a hard problem to an easy one does not make the hard problem easy
- The entire argument fails: the "reduction" goes in the wrong conceptual direction

For HC ≤_p MSP to imply P = NP, we would need MSP to be at least as hard as HC. If MSP ∈ P, the reduction is a reduction from hard to easy, which is trivially possible and proves nothing.

### Error 3: Lack of Rigorous Algorithmic Proof

The polynomial-time algorithm for MSP is never rigorously proven to be:
1. **Correct**: The algorithm always produces the right answer
2. **Polynomial**: The time complexity bound is verified

Red flags identified:
- Heavy reliance on self-citation (~10 references to author's own work)
- Almost no engagement with contemporary complexity theory literature
- Does not use standard mathematical typesetting (TeX/LaTeX)
- The author himself showed uncertainty: "It seems our algorithm is a polynomial one"

These are known warning signs from Scott Aaronson's checklist for evaluating claimed mathematical breakthroughs.

### Error 4: Experimental Validation Instead of Mathematical Proof

From Jiang's later work (2014):

> "The MSP problem possesses a novel polynomial-time heuristic algorithm, which has undergone extensive test and always give the correct answer for all instances (more than 5 × 10^7) generated up to now. Although there is no broad consensus with proving the correctness of the polynomial-time heuristic algorithm for the MSP problem."

This explicitly states:
- The "proof" relies on empirical testing of >50 million cases
- There is **no rigorous mathematical proof** of correctness
- Testing finite cases cannot establish universal correctness

A polynomial-time algorithm that "works in practice" but lacks a correctness proof is not a valid proof of P = NP.

### Summary of Why the Proof Fails

| Issue | Description |
|-------|-------------|
| Undefined problem | MSP lacks formal definition, making verification impossible |
| Wrong direction | If MSP ∈ P, reduction from HC to MSP proves nothing |
| No correctness proof | Algorithm correctness is assumed, not proven |
| Experimental evidence | 50M test cases ≠ mathematical proof |
| No peer review | 10+ years without acceptance in peer-reviewed venues |

## References

- **Primary**: Jiang, X. (2013). "A Polynomial Time Algorithm for the Hamilton Circuit Problem." arXiv:1305.5976
- **Analysis**: Hacker News discussion (June 2, 2013): https://news.ycombinator.com/item?id=5785693
- **Catalog**: Woeginger's P vs NP list, Entry #53: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Context**: Scott Aaronson's checklist for P=NP claims: https://www.scottaaronson.com/blog/?p=304
