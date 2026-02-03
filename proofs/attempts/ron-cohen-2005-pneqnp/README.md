# Formalization: Ron Cohen (2005) - P≠NP

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../../README.md)

---

## Metadata

- **Attempt ID**: 24 (from Woeginger's list)
- **Author**: Ron A. Cohen
- **Year**: 2005 (submitted November 25, 2005)
- **Claim**: P ≠ NP and P ⊂ NP ∩ co-NP
- **Paper**: [arXiv:cs.CC/0511085](https://arxiv.org/abs/cs.CC/0511085)
- **Title**: "Proving that P is not equal to NP and that P is not equal to the intersection of NP and co-NP"
- **Pages**: 9 pages, 3 figures

## Summary

Ron Cohen's 2005 paper claims to prove P ≠ NP by introducing two new machine models (D_new and ND_new) and proving they are not polynomially equivalent, which would imply standard Turing machines D and ND are not polynomially equivalent either.

## Main Argument/Approach

Cohen's proof strategy follows this structure:

### Step 1: Define New Machine Models

**D_new (New Deterministic Machine)**:
- Built from two tapes, each infinite in one direction
- First tape: "Regular Tape" with read-write cursor
- Second tape: "Hidden Tape" with **write-only** cursor (critical feature)
- "Input Button" (0/1): determines whether input goes to Regular (0) or Hidden (1) tape
- "Interrupt Button" (0/1): triggers comparison mechanism
- "Answer Button" (0/1): outputs comparison result
- **Interrupt mechanism**: compares word u on Regular Tape with word w on Hidden Tape; writes 1 to Answer Button if u=w, else 0

**ND_new (New Nondeterministic Machine)**:
- Similar to D_new, but with nondeterministic branching
- From any state, can have up to 3 transitions (vs. 1 for D_new)
- Always assumes the "best" transition is chosen

### Step 2: Proof Structure (Figure 1)

Cohen proves:
1. D ≡ D_new (D polynomially equivalent to D_new)
2. ND ≡ ND_new (ND polynomially equivalent to ND_new)
3. D_new ≢ ND_new (D_new NOT polynomially equivalent to ND_new)
4. Therefore: D ≢ ND (i.e., P ≠ NP)

### Step 3: The Separation Problem "Q"

Cohen defines decision problem Q:
- **Input**: "1" on Input Button (so input w goes to Hidden Tape), nothing on Regular Tape
- **Question**: Does there exist u ∈ Σ* such that w = 1·u (i.e., does w start with "1")?

**Key claims**:
- Q can be solved in polynomial time by ND_new (nondeterministically guess the correct string)
- Q **cannot** be solved in polynomial time by D_new (must try all 2^|w| possible strings in worst case)

### Step 4: Proof of P ⊂ NP ∩ co-NP

Cohen argues that problem Q:
- Cannot be decided in polynomial time (not in P)
- Has polynomial certificates for "yes" instances (in NP)
- Has polynomial certificates for "no" instances (in co-NP)

## The Critical Error

### The Fundamental Flaw: Non-Standard Computation Model

**The error occurs in the definition of the machine model itself.** Cohen's D_new and ND_new are **not** valid computation models equivalent to Turing machines because:

#### Error 1: The "Hidden Tape" Violates Computational Equivalence

The claim that D ≡ D_new (proof step 1) is **false**. Here's why:

In proof (1)(b), Cohen attempts to show any problem solvable in polynomial time on D_new can be solved in polynomial time on D. His argument states:

> "Let 'A' be a problem that can be solved in polynomial time with D_new. Lets assume that the input is presented to the 'Hidden Tape'. The input cannot be read directly from the 'Hidden Tape', since its cursor is write-only. In order to reveal the word, [exponential time steps needed]. Therefore, 'A' is presented to the 'Regular Tape', and it can be solved in polynomial time with D, in the same way."

**This is circular reasoning.** Cohen concludes that problems presented to the Hidden Tape must instead be presented to the Regular Tape, but this changes the problem instance itself. The equivalence D ≡ D_new requires that **for any problem A**, if A can be solved in poly-time on one machine, it can be solved in poly-time on the other **with the same input encoding**.

#### Error 2: The Input Encoding Matters

Cohen's construction conflates:
- **Problem specification** (what we're trying to compute)
- **Input encoding** (how the input is presented)

A valid polynomial equivalence must preserve the input encoding. You cannot say "D_new solves A when input is on Hidden Tape in polynomial time, and D solves A when input is on Regular Tape in polynomial time, therefore they're equivalent." These are **different computational tasks**.

#### Error 3: The "Interrupt Mechanism" is an Oracle

The interrupt mechanism that compares the Hidden Tape with the Regular Tape is effectively an **oracle** that provides information not computationally accessible to a standard Turing machine. This is similar to proving P ≠ NP by introducing an oracle and showing P^O ≠ NP^O, which tells us nothing about unrelativized P vs NP (Baker-Gill-Solovay, 1975).

#### Error 4: Problem Q is Not Well-Defined for Standard Turing Machines

The problem Q is specifically crafted to exploit the Hidden Tape mechanism. When Cohen claims there exists a "compatible problem" Q̃ for standard Turing machines, this compatibility is never rigorously defined. What does it mean for a problem to be "compatible"? This is hand-waving.

### Why This Doesn't Prove P ≠ NP

Even if we accept that D_new ≢ ND_new (which may be true for these non-standard machines), this tells us **nothing** about whether D ≢ ND because:

1. The polynomial equivalence D ≡ D_new is not properly established
2. The machines are not modeling the same computational framework
3. The separation relies on features (Hidden Tape) that don't exist in standard models

### Analogy

This is like claiming to prove something about cars by:
1. Defining "car_new" which has an invisible engine you can only detect by comparison
2. Showing car_new ≢ racecar_new based on the invisible engine
3. Claiming therefore car ≢ racecar

The error is that car_new is not actually equivalent to car in any meaningful sense.

## Formalization Status

### Rocq (`rocq/`)
- Status: Error identified during formalization
- Key issue: Cannot establish polynomial equivalence of D and D_new

### Lean (`lean/`)
- Status: Error identified during formalization
- Key issue: Machine model not well-defined in standard complexity theory

### Isabelle (`isabelle/`)
- Status: Error identified during formalization
- Key issue: Circular reasoning in equivalence proof

## Known Refutation

While this specific attempt may not have a published refutation, the error pattern is well-known:
- **Relativization barrier** (Baker-Gill-Solovay, 1975): Techniques that relativize (work with oracles) cannot resolve P vs NP
- Cohen's Hidden Tape with interrupt mechanism is effectively an oracle
- The proof technique relativizes and thus cannot prove P ≠ NP in the standard model

## Lessons Learned

1. **Machine equivalence must be rigorous**: Claims of polynomial equivalence require careful proof
2. **Input encoding matters**: You cannot change how inputs are presented and claim equivalence
3. **Oracle-like mechanisms don't help**: Features that act like oracles fall under relativization barrier
4. **Problem compatibility must be formal**: Hand-waving about "compatible problems" is insufficient

## References

### Original Paper
- Ron A. Cohen (2005). "Proving that P ≠ NP and P ⊂ NP ∩ co-NP". arXiv:cs.CC/0511085

### Related Barrier Results
- Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P =? NP Question." SIAM J. Comput.
- Razborov, A., Rudich, S. (1997). "Natural Proofs." J. Comput. System Sci.
- Aaronson, S., Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory." STOC

### Source
- Woeginger's P-versus-NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #24)

## License

This formalization is provided for research and educational purposes. See repository [LICENSE](../../../LICENSE).

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Parent Issue #44](https://github.com/konard/p-vs-np/issues/44) | [This Issue #118](https://github.com/konard/p-vs-np/issues/118)
