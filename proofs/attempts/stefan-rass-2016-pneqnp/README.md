# Stefan Rass (2016) - P≠NP Proof Attempt

**Attempt ID**: 111 (Woeginger's list)
**Author**: Stefan Rass
**Year**: 2016 (updated 2023)
**Claim**: P≠NP (via existence of weak one-way functions)
**Paper**: [arXiv:1609.01575v4](https://arxiv.org/abs/1609.01575)
**Status**: **FLAWED** - Contains logical gaps and circular reasoning

## Summary

This paper attempts to unconditionally prove the existence of weak one-way functions (OWFs), which would imply P≠NP. The approach uses the Time Hierarchy Theorem to construct hard decision problems, combines them with threshold sampling techniques from random graph theory, and builds a weak OWF by encoding bits as intractable problem instances.

## Main Argument

### 1. Foundation: Time Hierarchy Theorem

The proof starts with the deterministic Time Hierarchy Theorem, which guarantees the existence of a language L_D that:
- L_D ∈ DTIME(2^n) \ DTIME(t(n))
- Where t(n) = L_n[1, 1/2] = 2^(log(n)^(1/2) · (log log n)^(1/2)) (subexponential but superpolynomial)

This language L_D is constructed via diagonal argument (Section 4.3).

### 2. Density Control via Intersection with Squares

To control the density (frequency of yes-instances), the author constructs:
- **L_0 = L_D ∩ SQ** where SQ = {y : ∃x ∈ ℕ such that y = x²}
- This gives upper bound: dens_L0(x) ≤ √x (Lemma 4.7)
- And lower bound: dens_L0(x) ≥ d·ˣ√β for some constant d > 0, β ≥ 6 (Lemma 4.10)

### 3. Threshold Sampling

Using results from random graph theory (Theorem 4.12), the author develops a threshold sampling algorithm (Algorithm 3) that can:
- **Generate yes-instances** (sets W where W ∩ L_0 ≠ ∅) with probability → 1
- **Generate no-instances** (sets W where W ∩ L_0 = ∅) with probability → 1
- **Without** explicitly deciding membership in L_0
- In polynomial time

The threshold m* depends on:
- N: size of the universe to sample from
- p: density of L_0 within the universe
- Drawing m < m*/θ elements gives Pr(no-instance) → 1
- Drawing m > θ·(m* + 1) elements gives Pr(yes-instance) → 1

### 4. OWF Construction

The weak OWF f_ℓ : {0,1}^ℓ → (sets)^n maps each input bit to a sampled set:
- Input: w = b_1 b_2 ... b_n (plus random coins ω)
- Output: f_ℓ(w) = (W_1, W_2, ..., W_n)
- Where W_i ← PTS AMP(b_i, n, ω) samples a yes-instance if b_i=1, no-instance if b_i=0

### 5. One-Wayness Argument

The author argues (Section 4.8) that:
1. Inverting f_ℓ requires correctly recovering at least the first bit b_1
2. This is equivalent to deciding the language L_N (Lemma 4.18 + conditioning on event E_ℓ)
3. Any circuit C that decides L_N could be used to decide L_0, then L_D
4. But L_D was constructed to be hard for circuits of polynomial size
5. Using the "wasteful encoding" (Section 4.2), the worst-case occurs with frequency ≥ 1/(4ℓ)
6. Therefore, no polynomial-size circuit can invert f_ℓ with probability > 1 - 1/poly(ℓ)

### 6. Conclusion

If weak OWFs exist, then P≠NP (claimed in Corollary 5.1, "proven" in Section 5.6).

## Critical Errors and Gaps

### Error 1: Mismatch Between L_D Definition and Encoding

**Location**: Sections 4.2, 4.3, 4.8

**The Problem**:
- The diagonal language L_D (equation 9) is defined on inputs where a TM M_w processes ρ(M_w), the "functional prefix" encoding the TM
- The "wasteful encoding" (Figure 2) pads this with exponentially many bits to make equivalent encodings abundant
- However, for the diagonalization to work, M_w must reject "itself" - but which "self"?
  - If it's the short encoding ρ(M_w), then the padding doesn't help with frequency
  - If it's the full padded word w, then it's not actually simulating "itself" but a modified version

**Why This Matters**: The author needs the worst-case (diagonalization failure) to occur frequently (≥ 1/poly(ℓ)) to satisfy the weak OWF definition. The wasteful encoding is supposed to provide this, but creates a logical inconsistency in what L_D actually contains.

**Formal Issue**: See Remark 4.5 where the author acknowledges this modification but doesn't adequately resolve the tension.

### Error 2: Circular Dependence in Density Bounds

**Location**: Sections 4.4, 4.5, Lemma 4.10

**The Problem**:
- The lower bound on dens_L0 (Lemma 4.10) relies on a polynomial reduction φ: SQ → L_0 (Lemma 4.8)
- This reduction pads words to make them squares while preserving L_D membership
- However, the reduction itself depends on having enough "room" to pad, which depends on the density
- The constants α, β in the threshold function depend on this density
- But the choice of threshold function affects which sets are sampled
- This creates a circular dependency where the construction assumes what it needs to prove

**Why This Matters**: The threshold sampling only works if the density bounds are accurate, but the density bounds assume the reduction works correctly for all relevant input sizes.

###Error 3: Relativization Escape is Incomplete

**Location**: Section 5.1, equation (51)

**The Problem**:
- The author recognizes the relativization barrier and attempts to modify the diagonal language definition
- The modification (equation 51) inverts the decision if an oracle was called
- However, this breaks the hierarchy theorem separation in ALL relativized worlds (even those that should separate P from NP)
- The author claims this "has no effect" in non-relativized worlds, but:
  - The construction of L_0 uses SQ, which involves arithmetic operations
  - Some of these could be viewed as "oracle calls" in an arithmetized setting
  - The boundary between "oracle use" and "normal computation" is not precisely defined

**Why This Matters**: The modification undermines confidence in the proof without actually resolving the relativization concern.

### Error 4: Asymptotic vs. Finite Gap

**Location**: Throughout Section 4.5, especially equations (29), (30)

**The Problem**:
- The threshold sampling guarantees work asymptotically (as N → ∞)
- The bounds show Pr(correct sampling) → 1 and Pr(incorrect sampling) → 0
- However, for the weak OWF property, we need Pr(correct) ≥ 1 - 1/q(ℓ) for ALL sufficiently large ℓ
- The "sufficiently large" threshold is not computed
- The convergence rate is not analyzed
- For finite ℓ, the probabilities might not satisfy the weak OWF definition

**Why This Matters**: Asymptotic statements don't directly imply the uniform bounds needed for the OWF definition (Definition 2.3).

### Error 5: Conditional Probability Confusion

**Location**: Section 4.8, especially around equation (41), Lemma 4.19

**The Problem**:
- The inversion argument is conditioned on event E_ℓ (that the sampling worked correctly)
- Lemma 4.19 shows Pr(A|E_ℓ) → Pr(A) as ℓ → ∞
- However, the author applies this to connect:
  - Pr(circuit fails | E_ℓ) with Pr(circuit fails)
  - Pr(correct sampling | worst-case input) with Pr(worst-case | correct sampling)
- These probability manipulations hide the fact that:
  - The circuit might succeed precisely when sampling fails
  - The events might be correlated in ways that break the independence assumptions

**Why This Matters**: The conditioning removes exactly the cases where inversion might be easy, potentially invalidating the hardness claim.

## Known Refutations and Critiques

### Status in the Literature

As of 2023:
- **No published refutation** found in peer-reviewed literature
- **No acceptance** in major venues (STOC, FOCS, CCC)
- The paper has been on arXiv since 2016 with 4 revisions (latest July 2023)
- **No citations** resolving the P vs NP question based on this work
- Community consensus: If this proof were correct, it would be major news

### Why No Explicit Refutation?

Several possible reasons:
1. **Subtle errors**: The proof is 51 pages with intricate probability arguments
2. **Barrier discussion**: Section 5 acknowledges and discusses relativization, algebrization, naturalization - showing awareness of obstacles
3. **Self-refuting elements**: The modifications in Section 5.1 partially undermine the earlier arguments
4. **Lack of peer review**: ArXiv papers don't undergo formal peer review

### Our Assessment

The proof attempt contains **multiple significant gaps**:
1. Logical inconsistency in the encoding scheme (Error 1)
2. Circular reasoning in density bounds (Error 2)
3. Incomplete resolution of relativization (Error 3)
4. Asymptotic vs. finite gap (Error 4)
5. Conditional probability issues (Error 5)

Any ONE of these would be sufficient to invalidate the proof. The combination makes it highly unlikely that the approach can be repaired without fundamental changes.

## Formalization Strategy

Our formalization will:

1. **Coq**: Focus on the Time Hierarchy Theorem and density bounds (Sections 4.3-4.4)
2. **Lean**: Formalize the threshold sampling algorithm and probability bounds (Section 4.5)
3. **Isabelle**: Formalize the OWF construction and one-wayness argument (Sections 4.7-4.8)

In each system, we will:
- Precisely state all definitions and theorems
- Attempt to prove each step
- **Document where the proof gets stuck** (exposing the gaps)
- Provide counterexamples or impossibility arguments where applicable

## Key Definitions

### Weak One-Way Function (Definition 2.3)

A length-regular function f: Σ* → Σ* with polynomially related input/output lengths is a **weak one-way function** if:
1. f is computable in polynomial time
2. ∃ polynomial q ≥_asymp 0 such that ∀ polynomial p:
   - ∀ sufficiently large ℓ
   - ∀ circuit C with size(C) ≤ p(ℓ):
   - Pr[C(f_ℓ(w)) ∈ f_ℓ^(-1)(f_ℓ(w))] < 1 - 1/q(ℓ)

### Time Hierarchy Theorem (Theorem 4.6)

If t, T are fully time-constructible with:
- t(n) ≥ n
- lim_(ℓ→∞) (t(ℓ)·log t(ℓ))/T(ℓ) = 0
- t ≤ T

Then: DTIME(t) ⊊ DTIME(T)

### Threshold Function (Theorem 4.12)

For a monotone property Q of subsets of a set U with |U| = N:

Let m*(N) = max{k : Pr(Q_k) ≤ 1/2}

Then:
1. If m ≤ m*/θ(N): Pr(Q_m) ≤ 1 - 2^(-1/θ)
2. If m ≥ θ(N)·(m* + 1): Pr(Q_m) ≥ 1 - 2^(-θ)

## References

- **Primary Source**: Stefan Rass, "On the Existence of Weak One-Way Functions," arXiv:1609.01575v4 [cs.CC], July 2023
- **Woeginger's List**: Entry #111, https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Time Hierarchy**: Hopcroft & Ullman, "Introduction to Automata Theory, Languages and Computation" (1979)
- **OWF Theory**: Goldreich, "Foundations of Cryptography 1: Basic Tools" (2003)
- **Threshold Functions**: Bollobás & Thomason, "Threshold functions," Combinatorica 7(1):35-38 (1986)

## Formalization Progress

- [ ] Coq: Basic definitions (DTIME, time-constructible, G¨odel numbering)
- [ ] Coq: Time Hierarchy Theorem statement
- [ ] Coq: Density function properties
- [ ] Lean: Probability space for sampling
- [ ] Lean: Threshold function definition
- [ ] Lean: Threshold sampling algorithm
- [ ] Isabelle: OWF definition
- [ ] Isabelle: Weak OWF construction
- [ ] Isabelle: One-wayness proof attempt
- [ ] All: Document where proofs fail

## Conclusion

The Stefan Rass (2016) proof attempt is an interesting and sophisticated effort that engages deeply with complexity theory, probability, and the known barriers (relativization, algebrization, naturalization). However, it contains multiple fundamental gaps that prevent it from establishing P≠NP.

The formalization effort will make these gaps explicit and serve as a case study in:
1. Why P vs NP is so difficult
2. How subtle errors can hide in complex probabilistic arguments
3. The value of formal verification for catching logical flaws

**Status**: Formalization in progress
**Expected Outcome**: Proof will get stuck at multiple points, exposing the logical gaps
