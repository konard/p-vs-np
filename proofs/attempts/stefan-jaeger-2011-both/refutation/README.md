# Refutation: Stefan Jaeger (2011) - "Computational Complexity on Signed Numbers"

This directory contains the formal refutation of Stefan Jaeger's claimed proofs that P=NP (with the first Peano axiom) and P≠NP (without it).

## Overview

Jaeger's paper makes two claims using a non-standard number representation ("b-numbers"):
1. **Theorem 3**: P=NP (with first Peano axiom)
2. **Theorem 4**: P≠NP (without first Peano axiom)

Both claims fail, for the reasons documented below and formalized in the Lean/Rocq files.

## Refutation of Theorem 3 (P=NP Claim)

### The Claimed Proof

Jaeger argues: the first Peano axiom fixes the sign bit, so computations are either exponential or polynomial. By "assuming input bits are correct," we can use the polynomial case. Therefore P=NP.

### Why It Fails

**The machine does not decide any language.**

Jaeger's key statement is: *"T does not need to solve the problem in its entirety. It just needs to run until the required uncertainty is reached, after which it can output any result bit."*

This means T is permitted to output an **arbitrary** accept/reject bit after padding its input. A machine that outputs arbitrary bits is not a valid decision procedure for any language. In particular:
- For any NP-complete language L, a correct P algorithm must output "accept" on inputs in L and "reject" on inputs not in L.
- Jaeger's T makes no such guarantee — it just outputs any bit.

**The equivalence is not between computations on the same input.**

Theorem 2 (entropy reduction) produces an "equivalent computation" C' by applying a bijective mapping M to the input, giving a new input M(b). This is NOT computing the same function on the same input b. Saying C and C' are "equivalent" in Jaeger's sense means they have the same output bit — but this only holds because M can be chosen to make any output bit achievable, not because C' correctly solves the problem on the original input b.

**No P algorithm for NP-complete problems is produced.**

The paper does not exhibit a concrete polynomial-time algorithm for SAT, 3-coloring, or any other NP-complete problem. Without such an algorithm, the P=NP claim is unsubstantiated.

## Refutation of Theorem 4 (P≠NP Claim)

### The Claimed Proof

Jaeger defines a machine T(T', b) that reaches uncertainty I(1/(2b+1)) for T' accepting b. He claims T ∈ NP (O(2^n) steps suffice) but T ∉ P (by a diagonal argument with T'=T, b=T).

### Why It Fails

**T is claimed to be in NP for the wrong reason.**

NP consists of languages decidable in polynomial time by a nondeterministic Turing machine, or equivalently, languages with polynomial-length witnesses verifiable in polynomial time. Jaeger claims T ∈ NP because T can be implemented in O(2^n) time. But being solvable in exponential time does NOT imply membership in NP — EXP ≠ NP (by the time hierarchy theorem). Jaeger's argument confuses "solvable in exponential time" with "in NP."

**The diagonal argument is informal and imprecise.**

The argument sets T'=T and b=T (using the Gödel number of T as input). It claims that computing C=(T, TT, o) requires exponential steps to reduce the ratio of certain to uncertain bits below 1/(2b). However:
- The encoding of TT (the concatenation of T with itself as a Gödel number) and its relationship to the uncertainty bound is not formally established.
- The self-referential nature of the argument (T applied to its own code) requires careful treatment (as in the standard halting problem proof), but Jaeger provides only a hand-wavy description.
- The claim that exponential steps are *necessary* (not just sufficient) is not proven.

**The framework is not about standard P and NP.**

The uncertainty-based framework defines T as checking "whether T' accepts b with maximum uncertainty I(1/(2b+1))." This is not a standard language membership problem — it is a problem about uncertainty in encodings. The connection to the standard P vs NP question (about decision problems on deterministic/nondeterministic Turing machines) is never formally established.

## Refutation of the "Both" Meta-Claim

Jaeger claims both P=NP (with axiom 1) and P≠NP (without axiom 1) hold. This is an attempt to show the P vs NP question is "axiom-dependent." However:

1. **In any consistent extension of standard arithmetic**, either P=NP or P≠NP (exactly one). The two claims cannot both be correct about the *same* computational problems.

2. **Changing axioms creates a non-standard model.** Without the first Peano axiom, we are not working with standard natural numbers. The P vs NP problem is about computations on standard natural numbers, so the non-standard model's conclusions do not apply.

3. **Encoding invariance:** If b-numbers are polynomial-time convertible from/to standard binary (as they are — you just read or drop the sign bit in O(n) time), then the P and NP defined over b-numbers are identical to the standard P and NP. This means the "different axiom systems" produce the same computational complexity, and both claims cannot resolve the standard P vs NP question.

## Key Flaw Summary

| Claim | Stated Result | Actual Flaw |
|-------|--------------|-------------|
| Theorem 3 | P=NP (with Peano axiom 1) | Machine outputs arbitrary bits; does not decide any language |
| Theorem 4 | P≠NP (without Peano axiom 1) | NP membership argued incorrectly; diagonal argument is informal |
| Meta-claim | Both hold in different axiom systems | Non-standard model; encoding invariance shows standard P,NP unchanged |

## Files

- `lean/JaegerRefutation.lean` — Lean 4 formalization of the refutation
- `rocq/JaegerRefutation.v` — Rocq (Coq) formalization of the refutation
