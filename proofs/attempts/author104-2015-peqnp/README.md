# Frank Vega's P = NP Proof Attempt (2015)

**Attempt ID**: 104
**Author**: Frank Vega
**Year**: 2015
**Claim**: P = NP
**Paper**: "Solution of P versus NP Problem"
**Source**: https://hal.science/hal-01161668

## Overview

In June 2015, Frank Vega published a paper claiming to prove P = NP by introducing a new complexity class called **equivalent-P**. The proof attempts to show that equivalent-P equals both NP and P, which would imply P = NP.

## Main Argument

### Definition of equivalent-P

The complexity class **equivalent-P** is defined as the set of languages that contain ordered pairs of instances, where:
- Each element of the pair belongs to a specific problem in P
- The two instances share the same solution (i.e., the same certificate)

Formally, a language L is in equivalent-P if:
```
L = {(x₁, x₂) | x₁ ∈ L₁, x₂ ∈ L₂, L₁ ∈ P, L₂ ∈ P, cert(x₁) = cert(x₂)}
```

where `cert(x)` represents the certificate (solution) for instance x.

### Claimed Theorems

The paper claims to prove two main results:

1. **equivalent-P = NP**: Every language in equivalent-P is in NP, and vice versa
2. **equivalent-P = P**: Every language in equivalent-P is in P, and vice versa

### Conclusion

From these two theorems, the paper concludes:
```
P = equivalent-P = NP
```
Therefore, P = NP.

## The Error in the Proof

The fundamental flaw in this approach lies in the **definition and construction of equivalent-P**. Several critical issues emerge:

### 1. Certificate Ambiguity

The definition assumes that there exists a unique, well-defined notion of a "certificate" for problems in P. However:
- Problems in P don't require certificates for verification (they can be solved directly in polynomial time)
- The concept of "same certificate" is not rigorously defined for arbitrary P problems
- Different P problems may have incompatible certificate structures

### 2. Circular Reasoning in equivalent-P = NP

The claim that equivalent-P = NP contains circular logic:
- To show equivalent-P ⊆ NP: The proof must demonstrate that verifying whether two instances share the same certificate can be done in polynomial time
- To show NP ⊆ equivalent-P: The proof must show that any NP problem can be represented as pairs of P instances with shared certificates
- This second direction is particularly problematic, as it assumes what needs to be proved (that NP problems can be reduced to P)

### 3. The equivalent-P = P Claim

The claim that equivalent-P = P is highly suspect:
- Just because individual components (x₁, x₂) come from P problems doesn't mean the pairing relation is efficiently computable
- Determining whether two instances share the same certificate could be computationally hard
- The proof likely conflates "membership of individual elements in P" with "membership of the pair in P"

### 4. Loss of Computational Hardness

The construction fails to preserve the computational hardness of NP-complete problems:
- NP-complete problems are characterized by the difficulty of finding solutions, not just verifying them
- Representing NP problems as pairs of P instances with shared certificates doesn't capture the computational complexity of the original problem
- The pairing mechanism doesn't provide a polynomial-time algorithm for solving NP-complete problems

### 5. Known Complexity Barriers

The proof does not address known barriers to resolving P vs NP:
- **Relativization** (Baker-Gill-Solovay, 1975): The proof technique should fail in some oracle worlds if it's to overcome relativization
- **Natural Proofs** (Razborov-Rudich, 1997): Circuit lower bound proofs face fundamental obstacles
- **Algebrization** (Aaronson-Wigderson, 2008): Extended limitations on proof techniques

The paper does not demonstrate awareness of or engagement with these fundamental obstacles.

## Formal Verification Objective

The formalizations in this directory aim to:

1. **Formalize the definitions**: Precisely encode the definition of equivalent-P in Coq, Lean, and Isabelle
2. **Attempt the proofs**: Try to formalize the claimed theorems
3. **Identify the gap**: The formalization process will reveal where the proof breaks down
4. **Document the failure**: Clearly show why equivalent-P = P or equivalent-P = NP cannot be proven

## Expected Outcome

We expect that formalizing this proof will reveal that:
- The definition of "shared certificate" cannot be made rigorous for arbitrary P problems
- The proof that equivalent-P = NP contains an unjustified step
- The proof that equivalent-P = P requires solving an NP-hard problem
- Therefore, the claimed equality P = NP cannot be established through this approach

## Related Work

Frank Vega has published multiple attempts at resolving P vs NP using various approaches:
- Some claiming P = NP
- Others claiming P ≠ NP
- Various papers on related complexity theory topics

None of these attempts have been accepted by the complexity theory community, and several have been refuted or shown to contain errors.

## References

1. Vega, F. (2015). "Solution of P versus NP Problem". HAL Archives. https://hal.science/hal-01161668
2. Cook, S. A. (1971). "The complexity of theorem-proving procedures". STOC 1971.
3. Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P =? NP Question". SIAM Journal on Computing.
4. Razborov, A. A., & Rudich, S. (1997). "Natural proofs". Journal of Computer Science and Systems.
5. Aaronson, S., & Wigderson, A. (2008). "Algebrization: A new barrier in complexity theory". STOC 2008.

## Directory Structure

```
proofs/attempts/author104-2015-peqnp/
├── README.md                 # This file
├── coq/
│   └── EquivalentP.v        # Coq formalization
├── lean/
│   └── EquivalentP.lean     # Lean 4 formalization
└── isabelle/
    └── EquivalentP.thy      # Isabelle/HOL formalization
```

## Status

This formalization is part of the systematic effort to formally verify all P vs NP proof attempts listed in Woeginger's catalog. By formalizing both correct and incorrect proofs, we build a comprehensive understanding of proof techniques and common pitfalls in complexity theory.
