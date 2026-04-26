# THE ANSWER TO THE P/NP PROBLEM IS P≠NP!

**Author**: Bangyan Wen & Yi Lin
**Year**: 2010
**Source**: Scientific Inquiry — A Journal of the IIGSS, Vol. 11, No. 2, December 2010
**URL**: http://www.iigss.net/Scientific-Inquiry/Dec2010/table.htm

---

**Note**: The original paper is published in the IIGSS (International Institute for General Systems Studies) journal and is not freely available in a standard digital archive. The following is a reconstruction of the paper's content based on the Woeginger list description and the general approach described as "formal logic reasoning and analysis." The paper is listed as entry #70 on Woeginger's P vs NP list.

---

## Reconstructed Content (Based on Available Sources)

### Abstract (Reconstructed)

This paper addresses the famous P vs NP problem by applying formal logic reasoning and analysis. We examine the formal definitions of the complexity classes P and NP and show through logical argumentation that P ≠ NP. Our approach uses the structural asymmetry between deterministic polynomial-time computation and non-deterministic polynomial-time verification to establish the inequality.

---

### 1. Introduction

The P vs NP problem is one of the most important open problems in mathematics and computer science. This paper attempts to resolve this question using formal logic reasoning.

We recall the basic definitions:

**Definition 1.1 (Class P)**: A decision problem L is in P if and only if there exists a deterministic Turing machine M and a polynomial p such that for all inputs x:
- M halts on input x in at most p(|x|) steps
- M accepts x if and only if x ∈ L

**Definition 1.2 (Class NP)**: A decision problem L is in NP if and only if there exists a deterministic Turing machine V (a verifier) and a polynomial p such that for all inputs x:
- x ∈ L if and only if there exists a certificate c with |c| ≤ p(|x|) such that V(x, c) accepts in at most p(|x|) steps

---

### 2. Formal Logic Analysis

**Observation 2.1**: The membership condition for P can be written as:
```
x ∈ L ↔ ∃ computation path π of length ≤ p(|x|) : M_π(x) = ACCEPT
```
where the computation is *deterministic*, meaning there is a unique path π.

**Observation 2.2**: The membership condition for NP can be written as:
```
x ∈ L ↔ ∃ certificate c, |c| ≤ p(|x|) : V(x, c) = ACCEPT
```
where the certificate c ranges over an exponentially large search space.

**Claim 2.3**: The existential quantifier in NP ranges over an exponential-size domain (all certificates of polynomial length), while the existential quantifier in P ranges over only the unique deterministic computation.

---

### 3. The Main Argument

**Argument**: In P, the accepting witness (computation) is *unique and deterministically constructible*. In NP, the accepting witness (certificate) may be *non-uniquely defined* and requires searching through exponentially many candidates.

Formal logic tells us that:
- A problem in P has the form: ∃! computation in poly-time
- A problem in NP has the form: ∃ certificate among exponentially many

Since NP problems require searching through exponentially many certificates, and no deterministic polynomial-time algorithm can enumerate exponentially many candidates in polynomial time, NP problems cannot be solved in polynomial time by deterministic machines.

**Conclusion**: P ≠ NP.

---

### 4. Conclusion

Using formal logic reasoning and analysis of the structural definitions of P and NP, we have shown that P ≠ NP. The fundamental asymmetry between deterministic computation and non-deterministic verification means the two classes are distinct.

---

## Notes on the Reconstruction

This document is a reconstruction based on:
1. The Woeginger list description: the paper "employed formal logic reasoning and analysis"
2. The paper title: "THE ANSWER TO THE P/NP PROBLEM IS P≠NP!"
3. The general journal context (IIGSS, interdisciplinary, general systems theory)
4. Common patterns in formal-logic-based P≠NP attempts

The actual paper may contain additional material. The reconstruction focuses on the most likely core argument given the described methodology.
