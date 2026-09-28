# Original Paper: Approximation Resistance by Disguising Biased Distributions

**Author:** Peng Cui
**Year:** 2014 (submitted January 2014)
**arXiv ID:** [arXiv:1401.6520](https://arxiv.org/abs/1401.6520)
**Woeginger's List:** Entry #98 (also listed as #103 in extended list)
**Note:** The paper went through 24 versions on arXiv, with versions v2 and v21 withdrawn.

---

## Abstract

The paper claims to prove P = NP by showing that the gap problem of 3-XOR can be solved
by running Charikar & Wirth's semidefinite programming (SDP) algorithm for two rounds.
Since Gap 3-XOR is NP-hard (a consequence of the PCP theorem and hardness of approximation),
a polynomial-time algorithm for it would imply P = NP.

---

## Paper Content

### 1. Introduction and Motivation

The paper addresses the approximation resistance of constraint satisfaction problems (CSPs),
specifically 3-XOR (also known as Max-3-Lin-2 or Max-3-XOR). A CSP is called
**approximation-resistant** if no polynomial-time algorithm can achieve approximation ratio
better than random assignment.

The key question addressed: Is 3-XOR approximation-resistant?

**Background on 3-XOR:**
- Each clause is of the form $x_i \oplus x_j \oplus x_k = b$ for variables $x_i, x_j, x_k \in \{0,1\}$
  and $b \in \{0,1\}$
- A random assignment satisfies exactly 1/2 of the clauses in expectation
- It is known that for any $\varepsilon > 0$, it is NP-hard to distinguish instances where
  $(1-\varepsilon)$-fraction is satisfiable from instances where at most $(1/2+\varepsilon)$-fraction
  is satisfiable (Gap-3-XOR hardness)

**Background on dictator tests:**
A dictator test is a key tool in hardness of approximation. A function $f:\{-1,1\}^n \to \{-1,1\}$
is a dictator if $f(x) = x_i$ for some coordinate $i$. Dictator tests check whether a function
is a dictator or "far" from all dictators.

### 2. Technical Ingredients

The paper uses three main technical ingredients:

#### 2.1 Disguising the Verifier's Questions

The paper addresses a key issue in dictator tests: disguising the questions of the verifier
to a **balanced pairwise independent distribution**. The idea is to mask the structure of
the test so that the verifier's distribution looks uniform.

#### 2.2 Variance-Style Theorem

The paper uses a variance-style theorem to eliminate correlation of answers of all players
based on Label-Cover and its reflection version. This is used to show that any "good" strategy
for the provers must essentially use a dictator function.

**Label-Cover Problem:**
- Given a bipartite graph with left vertices $U$ and right vertices $V$
- Alphabet sets $\Sigma_U$ and $\Sigma_V$ for labels
- Projection constraints $\pi_e: \Sigma_U \to \Sigma_V$ for each edge $e$
- Goal: Find labelings $\ell_U: U \to \Sigma_U$ and $\ell_V: V \to \Sigma_V$ maximizing
  satisfied constraints

#### 2.3 Three Truncated Biased Pairwise Independent Distributions

The paper constructs three specific distributions $D_1, D_2, D_3$ over $\{-1,1\}^3$ that are:
- **Pairwise independent**: any two coordinates are independent
- **Biased**: the marginal distribution of each coordinate has a specific bias
- **Truncated**: modified to have certain properties needed for the proof

These distributions are used in the construction of the PCP verifier.

#### 2.4 The SDP Algorithm Approach

The paper claims that **Charikar & Wirth's SDP algorithm**, when run for **two rounds** on
the gap problem of 3-XOR, can solve it exactly (rather than just approximately).

**Charikar-Wirth Algorithm:**
Charikar and Wirth (FOCS 2004) gave an SDP-based algorithm for Max-k-CSP that achieves
approximation ratio $\Omega(k/2^k \cdot \log k)$. For Max-2-CSP this gives a constant-factor
approximation better than random.

The paper claims:
> "Running Charikar & Wirth's SDP algorithm for two rounds on the gap problem of some
> 3-XOR proves that this NP-hard problem can be solved efficiently."

#### 2.5 No Direct Sum Technique

The paper explicitly avoids the **direct sum technique** which requires the subgroup property
(a standard tool in hardness of approximation). Instead, the construction uses the biased
pairwise independent distributions directly.

### 3. The Claimed Proof Structure

The paper's argument proceeds as follows:

**Step 1:** Construct a PCP verifier for 3-XOR using the three truncated biased pairwise
independent distributions.

**Step 2:** Show that the verifier's distribution, after disguising (masking), looks like
a balanced pairwise independent distribution to the provers.

**Step 3:** Apply the variance-style theorem to show that optimal strategies for the provers
must use dictator functions.

**Step 4:** Use Charikar & Wirth's SDP algorithm (run for 2 rounds) to solve the resulting
gap problem in polynomial time.

**Step 5:** Conclude that Gap 3-XOR is in P, and since Gap 3-XOR is NP-hard, this implies P = NP.

### 4. Why the Author Believes the Proof Works

The author argues that:
- The disguising technique prevents the provers from exploiting the structure of the test
- The variance-style theorem forces optimal strategies to be dictator-like
- The two-round SDP captures enough information to exactly solve the gap problem
- The combination of these ingredients closes the gap in previous approaches

### 5. The Core Technical Claim

The central claim that, if true, would imply P = NP:

> **Claim:** The Charikar-Wirth SDP algorithm, when applied for 2 rounds to the gap instance
> of 3-XOR constructed via the three truncated biased pairwise independent distributions,
> achieves exact optimum (not just approximation).

Equivalently: there exists a polynomial-time algorithm (the 2-round SDP) that can distinguish
between:
- YES instances: at least $(1-\varepsilon)$ fraction of 3-XOR clauses can be satisfied
- NO instances: at most $(1/2+\varepsilon)$ fraction of 3-XOR clauses can be satisfied

for some $\varepsilon > 0$.

---

## Key Mathematical Objects

### 3-XOR (Max-3-Lin-2)

Given:
- Variables $x_1, \ldots, x_n \in \{0,1\}$
- Clauses of the form $x_i \oplus x_j \oplus x_k = b$ for $b \in \{0,1\}$

Goal: Find assignment maximizing number of satisfied clauses.

**Random assignment satisfies:** exactly $1/2$ of all clauses.
**NP-hardness of approximation:** For any $\varepsilon > 0$, it is NP-hard to distinguish
instances where $(1-\varepsilon)$-fraction is satisfiable from instances where at most
$(1/2+\varepsilon)$-fraction is satisfiable.

### Gap-3-XOR Problem

A promise problem:
- **YES instances:** $\text{OPT}(I) \geq 1 - \varepsilon$
- **NO instances:** $\text{OPT}(I) \leq 1/2 + \varepsilon$
- **Hardness:** By the PCP theorem and Hastad's 3-bit PCP, Gap-3-XOR is NP-hard

### Pairwise Independent Distribution

A distribution $(X_1, X_2, X_3)$ over $\{-1,1\}^3$ is **pairwise independent** if for all
$i \neq j$: $\mathbb{E}[X_i X_j] = 0$.

A **balanced** pairwise independent distribution additionally satisfies: $\mathbb{E}[X_i] = 0$
for all $i$.

### Charikar-Wirth SDP

The Charikar-Wirth algorithm (FOCS 2004) for Max-k-CSP:
- Formulates the problem as a semidefinite program (SDP)
- Runs the SDP to get a vector solution
- Rounds the vector solution to a binary assignment
- Achieves approximation ratio $\Omega(k/2^k \cdot \log k)$

---

## References

- **Primary source:** Peng Cui, "Approximation Resistance by Disguising Biased Distributions,"
  arXiv:1401.6520, 2014. Available at: https://arxiv.org/abs/1401.6520

- **Charikar-Wirth:** Moses Charikar and Anthony Wirth, "Maximizing quadratic programs:
  extending Grothendieck's inequality," FOCS 2004, pp. 54-60.

- **Hastad's 3-bit PCP:** Johan Håstad, "Some optimal inapproximability results,"
  Journal of the ACM, 48(4):798-859, 2001.

- **Woeginger's List:** Entry #98 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

- **PCP Theorem:** Arora, Lund, Motwani, Sudan, Szegedy (1998); Arora, Safra (1998)

---

*Note: This is a reconstruction of the paper's content based on its arXiv abstract, title,
and the description in Woeginger's list. The original PDF is in ORIGINAL.pdf in this directory.*
