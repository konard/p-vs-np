# Original Paper: Construction of an NP Problem with an Exponential Lower Bound

**Author:** Roman V. Yampolskiy
**Year:** 2011 (submitted November 1, 2011)
**arXiv ID:** [1111.0305](https://arxiv.org/abs/1111.0305)
**Subject Classification:** Computational Complexity (cs.CC)
**Woeginger's List:** Entry #77

---

## Abstract

In this paper we introduce the Hashed-Path Traveling Salesperson Problem (HPTSP), a variant of the well-known Traveling Salesman Problem, which can be verified in polynomial time but requires exponential time to solve. We provide proof that HPTSP is in NP but not in P. Via Ladner's theorem, as a consequence, the class of NP-intermediate problems (NPI) is non-empty, which implies that P ≠ NP.

---

## 1. Introduction

The traveling salesman problem (TSP) has been studied since the 1800s and is one of the most well-known combinatorial optimization problems. Despite significant effort, no polynomial time algorithm for TSP has been found. TSP belongs to the class NP and is known to be NP-complete.

In this paper, we introduce a variant of TSP, which we call the Hashed-Path Traveling Salesperson Problem (HPTSP). HPTSP was specifically designed to maintain the NP membership of TSP while making it provably outside of P.

The key idea: by replacing path costs with cryptographic hash values, we eliminate the "local information" that allows pruning in standard TSP, forcing any algorithm to examine all possible paths.

**Claim:** HPTSP ∈ NP \ P, which via Ladner's theorem implies P ≠ NP and NPI ≠ ∅.

---

## 2. Background

### 2.1 The Traveling Salesman Problem

**TSP Definition:** Given a complete graph G = (V, E) with edge costs, find the Hamiltonian cycle of minimum total cost.

- **Standard TSP**: Can be solved approximately; pruning-based approaches like branch-and-bound are effective in practice because edge weights provide local information.
- **Complexity**: TSP is NP-complete.

### 2.2 Complexity Classes

- **P**: Problems decidable in polynomial time.
- **NP**: Problems where solutions are verifiable in polynomial time.
- **NPI** (NP-Intermediate): Problems in NP but neither in P nor NP-complete (exists if P ≠ NP by Ladner's theorem, 1975).

### 2.3 Cryptographic Hash Functions

A cryptographic hash function h maps arbitrary-length strings to fixed-length strings:
- **Deterministic**: Same input always produces same output.
- **Fast to compute**: O(|input|) time.
- **Avalanche Effect / Strict Avalanche Criterion (SAC)**: Each output bit changes with probability 50% when any single input bit is flipped.
- **Preimage resistance**: Given h(x), it is computationally infeasible to find x.
- **Collision resistance**: It is computationally infeasible to find x ≠ y such that h(x) = h(y).

SHA-1 is used as the example hash function in this paper.

---

## 3. The Hashed-Path Traveling Salesperson Problem

### 3.1 Definition

**Input:** A complete graph G = (V, E) with edge costs c(e) ∈ ℕ for each edge e ∈ E, a cryptographic hash function h, and a string m.

**Encoding:** For a Hamiltonian cycle z = (v₁, v₂, ..., v_n, v₁), its encoding is the string:
```
encode(z) = "v₁" + c(v₁,v₂) + "v₂" + c(v₂,v₃) + ... + "v_n" + c(v_n,v₁)
```
where vertices are represented by their labels and edge costs are inserted between them.

**Question:** Does there exist a Hamiltonian cycle z such that h(encode(z)) ≤ m lexicographically?

Formally: `HPTSP = {⟨G, h, m⟩ : ∃ Hamiltonian cycle z in G such that h(encode(z)) ≤_lex m}`

### 3.2 Relationship to Standard TSP

HPTSP differs from TSP in a fundamental way:
- **TSP**: Optimizes actual path costs (additive function of edge weights).
- **HPTSP**: Optimizes lexicographic value of the hash of the encoded path.

In TSP, the cost of a sub-path provides direct information about the full path cost, enabling pruning. In HPTSP, due to the avalanche effect of hash functions, a sub-path provides no information about the hash value of the complete path.

---

## 4. HPTSP is in NP

**Claim:** HPTSP ∈ NP.

**Proof:**

Given a certificate (a Hamiltonian cycle z), verification proceeds as follows:

1. **Parse the certificate**: Extract the sequence of vertices from the encoded string. Time: O(|V|).
2. **Verify it is a valid Hamiltonian cycle**: Check all vertices appear exactly once. Time: O(|V|).
3. **Verify edge costs**: Check that each edge cost in the encoding matches the graph. Time: O(|V|).
4. **Compute the hash**: Apply h to the encoded string. Time: O(|V|) since h processes input linearly.
5. **Compare lexicographically**: Check that h(encode(z)) ≤_lex m. Time: O(|h output|) = O(1).

**Total verification time:** O(|V|), which is polynomial.

Since solutions can be verified in polynomial time, HPTSP ∈ NP. □

---

## 5. HPTSP is not in P

**Claim:** HPTSP ∉ P.

### 5.1 Key Property: No Local Information

**Lemma (Avalanche Effect):** For any cryptographic hash function h satisfying the Strict Avalanche Criterion, knowing encode(z₁) for a sub-path z₁ provides no information about h(encode(z)) for the complete path z.

*Reasoning:* Due to the avalanche effect, any single bit change in the input changes approximately 50% of output bits. The hash of a partial path bears no predictable relationship to the hash of the complete path. Therefore:

> "In the TSP case, each edge contains information about its length, a value which could be compared to other edges or even full paths to make decisions about pruning. In the case of the HPTSP edge information leaks no information about the value of the total solution... Because the information about local sectors is not sufficient to evaluate the complete path and can't be extracted or evaluated in relation to other sectors, no pruning of paths is possible."

### 5.2 Exponential Lower Bound

Since no pruning of paths is possible:

1. **No algorithm can eliminate any Hamiltonian cycle from consideration** without computing its complete hash value.
2. **There are |V|! Hamiltonian cycles** in a complete graph on |V| vertices.
3. **Each hash computation requires O(|V|)** time.
4. **Therefore, any algorithm requires Ω(|V|! · |V|)** time, which is superexponential.

*Supporting argument (compression):* Suppose the edge costs of an HPTSP instance are randomly generated. An ability to compute the full lexicographic order of an encoded path without examining all of it would essentially be the same as being able to compress a string of random numbers, which is a contradiction with the incompressibility of random strings.

> "This forces any algorithm to consider all possible paths in a search for an optimal solution, requiring an exponential lower bound for HPTSP."

**Conclusion:** HPTSP requires exponential time, so HPTSP ∉ P. □

---

## 6. Consequences

### 6.1 P ≠ NP

Since HPTSP ∈ NP and HPTSP ∉ P, there exists a problem in NP that is not in P. Therefore:

**Theorem:** P ≠ NP.

### 6.2 NPI is Non-Empty (via Ladner's Theorem)

**Ladner's Theorem (1975):** If P ≠ NP, then there exist NP-intermediate problems (problems in NP but neither in P nor NP-complete).

The paper claims that HPTSP is not NP-complete (because it lacks properties of NP-complete problems like natural reductions from other NP problems). Therefore, HPTSP ∈ NPI.

**Corollary:** The class NPI is non-empty.

---

## 7. Response to Potential Objections

### 7.1 "Could someone cryptanalyse the hash function?"

> "Could someone cryptanalyse the hash function and figure out how hash values are determined? Yes, but to obtain specific hash values a particular input string would need to be analyzed and there is an exponential number of such strings."

### 7.2 "What if the hash function is broken?"

The paper acknowledges SHA-1 has known vulnerabilities but argues:
- The collision vulnerabilities in SHA-1 do not affect the argument.
- Any cryptographic hash function satisfying the avalanche effect suffices.
- The argument is about the mathematical properties of hash functions, not specific implementations.

### 7.3 Connection to Circuit Complexity

The paper also suggests a connection to circuit complexity: since hash functions cannot be computed with short circuits (by assumption), no circuit of polynomial size can solve HPTSP.

---

## 8. Conclusion

The paper introduces HPTSP, a variant of TSP where path costs are replaced by hash values. Due to the avalanche effect of cryptographic hash functions, no pruning is possible, forcing algorithms to examine all O(n!) paths. This gives an exponential lower bound, placing HPTSP outside P. Since HPTSP ∈ NP, this proves P ≠ NP, and by Ladner's theorem, NPI ≠ ∅.

---

## References

1. Ladner, R. E. (1975). On the structure of polynomial time reducibility. *Journal of the ACM*, 22(1), 155-171.
2. Yampolskiy, R. V. (2011). Construction of an NP Problem with an Exponential Lower Bound. arXiv:1111.0305.
3. SHA-1: Secure Hash Algorithm 1. FIPS PUB 180-4.
4. Wang, X., Yin, Y. L., & Yu, H. (2005). Finding Collisions in the Full SHA-1. *CRYPTO 2005*.
5. Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.
