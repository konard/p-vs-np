# P vs NP

**Author:** Gilberto Rodrigo Diduch
**Year:** 2012 (January)
**Journal:** International Journal of Computer Science and Network Security (IJCSNS)
**Volume:** 12, No. 1, January 2012, pp. 165–167
**Woeginger's List:** Entry #81

---

> **Note:** The original paper is not freely accessible via standard academic databases.
> This document reconstructs the content based on information available from
> Woeginger's P-versus-NP list, the journal record, and standard descriptions of the work.
> The paper's title is "P vs NP" and it was published in IJCSNS Vol. 12, No. 1, 2012.

---

## Abstract (Reconstructed)

The paper claims to prove that P is not equal to NP. The author states that
"the answer to the P vs NP question is a categorical NO; these classes are different
as their names suggest."

---

## Main Argument (Reconstructed)

### Claim

The paper asserts that the complexity classes P and NP are fundamentally different,
and that this difference justifies concluding P ≠ NP.

### Core Statement

The central claim relies on the observation that:

1. **P** (Polynomial time) consists of decision problems solvable by a deterministic
   Turing machine in polynomial time.
2. **NP** (Nondeterministic Polynomial time) consists of decision problems whose
   solutions can be *verified* in polynomial time.
3. Because solving a problem is generally harder than verifying a solution,
   the paper concludes that P ≠ NP.

### Informal Argument Structure

The paper appears to argue along the following lines:

- Definition of P: problems solvable in polynomial time by a deterministic algorithm.
- Definition of NP: problems verifiable in polynomial time given a certificate.
- Observation: NP problems like SAT require checking exponentially many possible
  assignments in the worst case for any known deterministic algorithm.
- Conclusion: Since no polynomial-time algorithm is known for NP-complete problems,
  and since the class definitions are different, P ≠ NP.

### The Categorical Assertion

The abstract makes the categorical assertion: "the answer to the P vs NP question
is a categorical NO; these classes are different as their names suggest."

This assertion is the conclusion of the paper, treating the difference in the
*names* and *definitions* of P and NP as sufficient grounds for concluding
they are different classes.

---

## Publication Context

The paper was published in the International Journal of Computer Science and Network
Security (IJCSNS), a journal that has published a number of informal or non-peer-reviewed
complexity theory claims. It appears as entry #81 in Gerhard Woeginger's comprehensive
list of P vs NP proof attempts, which catalogues over 100 claimed proofs from 1986 to 2016.

---

## References in the Paper (Reconstructed)

1. Cook, S. A. (1971). The complexity of theorem-proving procedures. STOC.
2. Karp, R. M. (1972). Reducibility among combinatorial problems.
3. Garey, M. R., & Johnson, D. S. (1979). Computers and Intractability: A Guide to the
   Theory of NP-Completeness.

---

## Source

- **Woeginger's List:** https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #81)
- **Journal:** International Journal of Computer Science and Network Security (IJCSNS),
  Vol. 12, No. 1, January 2012, pp. 165–167
- **Note:** Thanks to Gordon Royle for providing the original link to this paper.
