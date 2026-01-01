# Singh Anand (2005) - P≠NP Proof Attempt

**Attempt ID**: 19
**Author**: Bhupinder Singh Anand
**Year**: 2005
**Claim**: P≠NP
**Status**: Unverified / Not accepted by research community

## Overview

In June 2005, Bhupinder Singh Anand published a paper titled "Is the Halting problem effectively solvable non-algorithmically, and is the Goedel sentence in NP, but not in P?" available from arXiv math.GM/0506126.

## Main Argument

Anand's proof attempts to show that P is not equal to NP under a specific provability assumption. The core argument involves:

1. **Provability Assumption**: Every Turing-decidable true arithmetical relation is provable in Peano Arithmetic (PA)

2. **Gödel's Predicate**: Anand treats Gödel's arithmetical predicate R(x) as a Boolean function

3. **Complexity Classification**: Claims to show that this Gödel predicate is in NP but not in P

4. **Connection to Halting Problem**: Suggests the Halting problem might be "effectively solvable non-algorithmically"

## The Approach

### Key Claims

1. First-order Peano Arithmetic has no non-standard models
2. All provable arithmetical formulas are Turing-decidable under the standard interpretation of PA
3. The set of Gödel-formulas of PA is empty
4. These results imply P≠NP

### Methodology

Anand attempts to build an "iff bridge" between:
- **Domain of Provability**: How human intelligence decides the truth of number-theoretic relations (formalized by first-order Peano Arithmetic PA)
- **Domain of Computability**: How computational systems solve problems

## Known Issues and Criticisms

### Problem 1: Strong Provability Assumption

The assumption that "every Turing-decidable true arithmetical relation is provable in Peano Arithmetic" is itself highly problematic:

- **Gödel's Incompleteness Theorems** show that PA cannot prove all true arithmetical statements
- There exist true but unprovable statements in PA (e.g., the Gödel sentence itself)
- This assumption contradicts fundamental results in mathematical logic

### Problem 2: Non-Standard Models

The claim that PA has no non-standard models contradicts well-established results in model theory:

- **Gödel's Completeness Theorem** and the **Compactness Theorem** guarantee the existence of non-standard models of PA
- Non-standard models of arithmetic are well-studied objects in mathematical logic
- The existence of non-standard models is a fundamental result, not something that can be disproven

### Problem 3: Confusion Between Provability and Computability

The argument appears to confuse or conflate:
- **Provability**: A syntactic notion (derivability in a formal system)
- **Computability**: A semantic notion (existence of algorithms)
- **Truth**: A semantic notion (satisfaction in models)

These are distinct concepts with different properties.

### Problem 4: Circular Reasoning

The argument relies on strong assumptions that would themselves require proof:
- Assumes properties about PA that contradict known results
- Uses these assumptions to derive conclusions about complexity classes
- The gap between provability in PA and complexity class membership is not properly bridged

### Problem 5: Non-Algorithmic Solvability

The suggestion that problems might be "effectively solvable non-algorithmically" is philosophically problematic:
- The Church-Turing thesis identifies effective computability with algorithmic computability
- While the thesis is not mathematically proven, alternative models of computation have not been shown to exceed Turing machines
- This claim would require extraordinary evidence

## Community Reception

- This paper appears on [Gerhard Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) of attempted P vs NP proofs (Entry #19)
- Woeginger's list tracks unverified/refuted attempts at solving P vs NP
- The proof has not been accepted by the research community
- No peer-reviewed publication in a major venue has validated these claims
- The work remains outside mainstream complexity theory

## Formalization Status

This directory contains formal verification attempts in:
- **Coq** (`coq/`)
- **Lean** (`lean/`)
- **Isabelle** (`isabelle/`)

The goal of formalization is to identify precisely where the argument fails and to demonstrate the logical gaps explicitly.

## Expected Outcome

The formalization is expected to reveal:
1. The incompatibility of the provability assumption with Gödel's Incompleteness Theorems
2. The contradiction with the existence of non-standard models of PA
3. The gap in connecting provability properties to complexity class separations
4. The precise point at which the argument becomes circular or relies on unjustified assumptions

## References

- **Original Paper**: Bhupinder Singh Anand. "Is the Halting problem effectively solvable non-algorithmically, and is the Goedel sentence in NP, but not in P?" arXiv:math/0506126 (June 2005)
- **Woeginger's List**: [P-versus-NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), Entry #19
- **Related Work**: Anand has published several related papers expanding on these themes, none accepted by mainstream complexity theory

## Educational Value

Attempting to formalize this proof provides valuable lessons in:
- The distinction between provability, computability, and truth
- Gödel's Incompleteness Theorems and their implications
- The properties of non-standard models of arithmetic
- Why seemingly plausible arguments can fail when subjected to formal verification
- The importance of rigorous foundations when working on fundamental problems

## Source

This formalization task is derived from [Issue #106](https://github.com/konard/p-vs-np/issues/106), part of the broader [Issue #44](https://github.com/konard/p-vs-np/issues/44) project to formally test all P vs NP proof attempts.
