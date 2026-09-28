# Joonmo Kim (2014) - P≠NP Attempt

**Attempt ID**: 100 (from Woeginger's list)
**Author**: Joonmo Kim
**Year**: 2014
**Claim**: P ≠ NP
**Paper**: [P not equal NP by modus tollens](http://arxiv.org/abs/1403.4143)

## Overview

In March 2014, Joonmo Kim proposed a proof that P ≠ NP using a modus tollens argument. The proof constructs an artificially designed Turing Machine that generates instances of the satisfiability problem and checks their satisfiability. The argument attempts to show that under the assumption P = NP, this machine would have a certain property that it demonstrably does not have, leading to P ≠ NP by contradiction.

## Main Argument

### The Approach

1. **Construction of Special Turing Machine**: The author designs a Turing machine M₀ that:
   - Generates SAT problem instances
   - Checks their satisfiability
   - Has specific computational properties

2. **Conditional Property**: Under the assumption that P = NP:
   - The machine M₀ would possess a particular computational property
   - This property relates to the machine's ability to solve SAT efficiently

3. **Contradiction via Modus Tollens**:
   - Show that M₀ does not actually have this property
   - Since M₀ lacks the property it would have if P = NP, conclude P ≠ NP
   - Form: (P=NP → Property(M₀)) ∧ ¬Property(M₀) → ¬(P=NP)

### Key Claims

The proof relies on establishing that:
- A specific Turing machine construction has well-defined properties
- These properties can be proven to hold or not hold
- The relationship between P = NP and these properties is valid

## Author's Self-Assessment

Notably, the author himself acknowledges significant concerns about the proof:

> "this solution should not be reported to be correct"

> "it is quite unlikely that this simple solution is correct"

The author explicitly requested community feedback to identify potential conceptual mistakes, indicating awareness that the proof likely contains errors.

## Known Issues and Likely Errors

Based on the paper and general principles of complexity theory, potential issues include:

### 1. Self-Reference and Diagonalization
- The construction appears to involve self-referential reasoning
- Similar to many failed P vs NP attempts that try to construct machines that reference their own behavior
- Such arguments often fall victim to the **Relativization Barrier** (Baker-Gill-Solovay, 1975)

### 2. Oracle Independence
- Any proof technique that relativizes (works in all oracle worlds) cannot resolve P vs NP
- There exist oracles A where P^A = NP^A and oracles B where P^B ≠ NP^B
- Arguments based solely on Turing machine properties often relativize

### 3. Insufficiently Rigorous Property Definition
- The "certain property" that M₀ would have under P = NP may not be formally well-defined
- Without precise definitions, the modus tollens argument cannot be verified
- Computational complexity requires extremely precise definitions to avoid circular reasoning

### 4. Confusion Between Decision and Construction
- Many failed proofs confuse:
  - Deciding if a solution exists (NP)
  - Constructing a solution efficiently (potentially harder)
  - Self-referential computation patterns

### 5. Oversimplification
- The author's own assessment that it is "quite unlikely that this simple solution is correct" is telling
- P vs NP has resisted 50+ years of attempts by world-leading researchers
- Genuinely novel techniques are needed that overcome known barriers

## Formalization Strategy

To identify the specific error, we formalize the proof in three theorem provers:

### Rocq (`rocq/`)
- Define Turing machines and complexity classes
- Formalize the construction of M₀
- Attempt to prove the key properties
- **Expected outcome**: Formalization will reveal circularity or undefined behavior

### Lean (`lean/`)
- Use Lean 4's modern dependent type theory
- Model computational complexity
- Formalize the modus tollens argument
- **Expected outcome**: Type system will reject insufficiently precise definitions

### Isabelle/HOL (`isabelle/`)
- Leverage Isabelle's mature complexity theory libraries
- Formalize oracle constructions to test relativization
- **Expected outcome**: Oracle-based counterexample or proof gap

## Formalization Files

- `rocq/JoonmoKim2014.v` - Rocq formalization
- `lean/JoonmoKim2014.lean` - Lean 4 formalization
- `isabelle/JoonmoKim2014.thy` - Isabelle/HOL formalization

## Expected Result

The formalization process is expected to reveal:
1. The exact point where the argument fails
2. Whether the proof relativizes (and thus cannot work)
3. Specific gaps in the definitions or reasoning
4. Educational insights about common pitfalls in P vs NP proof attempts

## Educational Value

This formalization serves multiple purposes:
- Demonstrates how formal verification can identify subtle errors
- Illustrates common mistakes in complexity theory proof attempts
- Shows the importance of accounting for known barriers
- Provides templates for analyzing other claimed P vs NP proofs

## References

1. **Original Paper**: Joonmo Kim (2014). "P not equal NP by modus tollens". arXiv:1403.4143. [http://arxiv.org/abs/1403.4143](http://arxiv.org/abs/1403.4143)

2. **Woeginger's List**: Gerhard J. Woeginger. "The P-versus-NP page". Entry #100. [https://www.win.tue.nl/~gwoegi/P-versus-NP.htm](https://www.win.tue.nl/~gwoegi/P-versus-NP.htm)

3. **Relevant Barriers**:
   - Baker, Gill, Solovay (1975). "Relativizations of the P =? NP Question". SIAM Journal on Computing.
   - Razborov, Rudich (1997). "Natural Proofs". Journal of Computer and System Sciences.
   - Aaronson, Wigderson (2008). "Algebrization: A New Barrier in Complexity Theory". STOC.

## Status

**Status**: Formalization in progress
**Goal**: Identify the specific error or gap in the proof attempt
**Method**: Multi-prover formal verification (Rocq, Lean, Isabelle)

---

*Part of the P vs NP Educational Research Repository*
*Issue #59 - Testing formal proof attempts*
*Parent Issue: #44 - Test all P vs NP attempts formally*
