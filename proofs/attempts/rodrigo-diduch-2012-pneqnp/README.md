# Rodrigo Diduch (2012) - P≠NP Proof Attempt

**Attempt ID**: 81 (from Woeginger's list)
**Author**: Gilberto Rodrigo Diduch
**Year**: 2012
**Claim**: P ≠ NP
**Status**: Refuted
**Publication**: International Journal of Computer Science and Network Security (IJCSNS), Volume 12, No. 1, January 2012, pp. 165–167

## Summary

In January 2012, Gilberto Rodrigo Diduch published a paper titled "P vs NP" in IJCSNS
claiming that P is not equal to NP. The paper states that "the answer to the P vs NP
question is a categorical NO; these classes are different as their names suggest."

This proof attempt is catalogued on Gerhard J. Woeginger's comprehensive list of P vs NP
proof attempts, which has tracked over 100 attempted proofs from 1986 to 2016.

## Source

- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #81)
- **Original Paper**: International Journal of Computer Science and Network Security (IJCSNS),
  Vol. 12, No. 1, January 2012, pp. 165–167
- **Link Note**: Thanks to Gordon Royle for providing the original link

## Main Argument

The paper argues informally that:

1. P consists of problems solvable in polynomial time by a deterministic algorithm.
2. NP consists of problems whose solutions can be *verified* in polynomial time.
3. Because solving a problem is generally harder than verifying a solution,
   and because no polynomial-time algorithm is known for NP-complete problems,
   the paper concludes that P ≠ NP.

The central claim is that the classes are "different as their names suggest" —
treating the difference in definitions as sufficient grounds for concluding the classes differ.

## The Error

### Fundamental Flaw: Argument from Definitions Without a Lower Bound Proof

**The Core Error**: Diduch's proof conflates *not knowing* a polynomial-time algorithm with
*proving that none can exist*. Observing that no polynomial algorithm for SAT is known does not
constitute a mathematical proof that no such algorithm exists.

### Why This Argument Fails

A valid proof of P ≠ NP requires establishing a **super-polynomial lower bound** for some
NP problem — proving that *no* Turing machine, regardless of construction, can decide the
problem in polynomial time.

What Diduch's argument provides instead:

| What the paper claims | What would be needed |
|----------------------|----------------------|
| P and NP have different definitions | Proof that different definitions imply different classes |
| No polynomial algorithm for SAT is known | Proof that NO polynomial algorithm can exist |
| NP problems "feel hard" | Formal circuit lower bound or similar impossibility result |

**Counterexample to the argument style**: Many pairs of classes have different definitions
yet turn out to be equal. For instance, the class of problems decidable in O(n²) time and
the class decidable in O(n³) time have different definitions but both are subclasses of P.
A difference in definition does not imply a difference in extension.

### The Missing Component: Super-Polynomial Lower Bound

For a valid P ≠ NP proof, one must show:

```
∀ TM. (TM decides SAT) → time(TM) ∉ polynomial
```

This is precisely the content that Diduch's paper does not establish.
The paper provides no lower bound argument, no circuit complexity argument,
no communication complexity argument, and no diagonalization argument.

### Absence of Evidence vs. Evidence of Absence

The paper's reasoning commits the logical fallacy of treating the current
*absence* of a known polynomial algorithm for NP-complete problems as
*evidence* that no such algorithm exists. Historical examples show that
many problems once thought to require exponential time were later solved
in polynomial time:
- Primality testing was solved in polynomial time (AKS, 2002)
- Linear programming was shown to be in P via the ellipsoid method (1979)
- Many graph problems once thought hard were later resolved

## Known Barriers Not Addressed

Any valid P ≠ NP proof must overcome these established barriers:

### 1. Relativization Barrier (Baker-Gill-Solovay, 1975)
- There exist oracles A and B such that P^A = NP^A and P^B ≠ NP^B
- Oracle-based proof techniques cannot resolve P vs NP
- Diduch's definitional argument relativizes and is therefore blocked

### 2. Natural Proofs Barrier (Razborov-Rudich, 1997)
- "Natural" circuit lower bound techniques cannot separate P from NP
  (assuming strong cryptography exists)
- Any successful proof must use non-naturalizing techniques

### 3. Algebrization Barrier (Aaronson-Wigderson, 2008)
- Extends relativization to algebraic computation models
- Further restricts available proof strategies

Diduch's proof addresses none of these barriers.

## Formalization Goal

This directory contains formal verification attempts in Lean 4 and Rocq to:

1. **Formalize the claimed proof structure** based on available information
2. **Identify logical gaps** through formalization
3. **Document why the proof attempt fails** in precise mathematical terms
4. **Serve as an educational example** of proof verification

## Formal Verification Status

- **Rocq**: See `proof/rocq/DiduchProof.v` and `refutation/rocq/DiduchRefutation.v`
- **Lean**: See `proof/lean/DiduchProof.lean` and `refutation/lean/DiduchRefutation.lean`

Each formalization:
1. Defines necessary complexity theory concepts
2. States the claimed theorem
3. Formalizes the proof steps
4. Marks incomplete steps with `Admitted`/`sorry`
5. Documents the specific error

## References

1. Baker, T., Gill, J., & Solovay, R. (1975). Relativizations of the P=?NP Question.
   SIAM Journal on Computing, 4(4), 431–442.
2. Razborov, A. A., & Rudich, S. (1997). Natural Proofs.
   Journal of Computer Science and System Sciences, 55(1), 24–35.
3. Aaronson, S., & Wigderson, A. (2008). Algebrization: A New Barrier in Complexity Theory.
   STOC '08.
4. Aaronson, S. (2010). Eight Signs A Claimed P≠NP Proof Is Wrong.
   https://scottaaronson.blog/?p=458
5. Woeginger, G. J. P-versus-NP page.
   https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Parent Issues

- Part of [#67](https://github.com/konard/p-vs-np/issues/67) - Formalize Rodrigo Diduch (2012) P≠NP attempt
- Part of [#44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
