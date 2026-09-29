# Original Proof: Jeffrey W. Holcomb (2011) - P≠NP via Stochastic Answers

**Author:** Jeffrey W. Holcomb
**Year:** 2011 (Fall)
**Original URL:** http://www.holcombtechnologies.com (no longer accessible)
**Source:** Woeginger's P versus NP page, Entry #79 (later renumbered #83)
**Claim:** P ≠ NP

---

> **Note:** The original papers by Jeffrey W. Holcomb were hosted at
> http://www.holcombtechnologies.com, which is no longer accessible. This markdown
> document reconstructs the proof argument based on:
> 1. Woeginger's description on the P versus NP page
> 2. Information provided by Peter Bro Miltersen
> 3. The known key paper title: "Just How Random Are Your Answers?"

---

## Abstract (Reconstructed)

Jeffrey W. Holcomb published a sequence of papers in Fall 2011 claiming to establish that
P ≠ NP. The central argument relies upon the existence of **stochastic answers** in the
set difference between NP and P (i.e., problems that are in NP but not in P).

The key paper in the sequence was titled **"Just How Random Are Your Answers?"**, which
appears to have argued that:

1. Problems solvable in polynomial time (P) produce **deterministic** answers
2. Problems in NP that are not in P must produce **stochastic** (random/probabilistic) answers
3. This distinction between deterministic and stochastic answers proves P ≠ NP

---

## Main Argument (Reconstructed)

### Setup

Let L be a decision problem (a language). We say:

- L ∈ P if there is a polynomial-time Turing machine M that decides L
- L ∈ NP if there is a polynomial-time verifier V and polynomial p such that:
  - x ∈ L ⟺ ∃w (|w| ≤ p(|x|)) such that V(x, w) = 1

### Claimed Key Definition: Stochastic Answer

Holcomb claimed to identify a property of the **answers** to problems in NP \ P that
distinguishes them from problems in P. This property was described as "stochastic" -
meaning the answers to such problems exhibit some form of randomness or probabilistic
character.

> "The proof relies upon the existence of stochastic answers in the set difference
> between NP and P." — Woeginger's description

The precise formal definition of "stochastic answer" was not given in terms that the
complexity theory community found acceptable.

### Claimed Argument Structure

**Step 1:** Define the notion of a "stochastic answer" for a decision problem.

**Step 2:** Prove that problems in P do NOT have stochastic answers:
- P problems have polynomial-time algorithms that produce definite YES/NO answers
- There is no randomness or stochasticity in the computation

**Step 3:** Prove that problems in NP \ P DO have stochastic answers:
- Problems like SAT, where we cannot efficiently determine the answer
- The key paper "Just How Random Are Your Answers?" argues that inability to solve
  efficiently leads to a form of stochasticity in the answers

**Step 4:** Conclude P ≠ NP:
- If P = NP, then every NP problem would be in P
- But P problems don't have stochastic answers
- Some NP problems have stochastic answers
- Contradiction: therefore P ≠ NP

### The Central Claim

The proof claims that **stochastic answers characterize exactly the problems in NP \ P**:

```
L ∈ NP \ P  ⟺  L has stochastic answers
```

From this characterization, P ≠ NP would follow immediately (since NP \ P would be
non-empty: it would contain all problems with stochastic answers).

---

## Key Paper: "Just How Random Are Your Answers?"

This was identified as the central paper in the sequence. Based on the title and the
description of the proof, it appears to have argued:

1. **Randomness of answers**: When we ask a YES/NO question that is "hard" (not in P),
   the answer exhibits properties of randomness

2. **The argument**: If we consider a uniform distribution over inputs of a given size,
   the distribution of YES/NO answers for NP-complete problems has high entropy or
   appears random in some sense

3. **The claimed separation**: This apparent randomness in answers is claimed to be
   provably absent from P problems, giving a formal separation

---

## Issues Identified (from Woeginger's page)

Woeginger listed this proof and noted that it "relies upon the existence of stochastic
answers in the set difference between NP and P" without providing further details about
accepted community refutation. The proof did not appear in peer-reviewed literature.

---

## Status

- **Not peer-reviewed**: The proof does not appear in any peer-reviewed venue
- **Not accepted**: Not accepted by the complexity theory research community
- **Website offline**: The original papers are no longer accessible
- **Fundamental gap**: The notion of "stochastic answer" was not formally defined in
  a way compatible with standard complexity theory

---

## References

1. Woeginger, G. J. "P-versus-NP page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
   (Entry #79, later renumbered)
2. Information provided by Peter Bro Miltersen (referenced on Woeginger's page)
3. Key paper title: "Just How Random Are Your Answers?" by Jeffrey W. Holcomb
