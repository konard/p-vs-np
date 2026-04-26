# Bangyan Wen & Yi Lin (2010) - P≠NP via Formal Logic Reasoning

**Attempt ID**: 70 (from Woeginger's list)
**Authors**: Bangyan Wen & Yi Lin
**Year**: 2010
**Claim**: P ≠ NP
**Status**: Refuted

## Summary

In December 2010, Bangyan Wen and Yi Lin published a paper titled "THE ANSWER TO THE P/NP PROBLEM IS P≠NP!" in the electronic journal "Scientific Inquiry - A Journal of the IIGSS" (International Institute for General Systems Studies). The paper employs "formal logic reasoning and analysis" to argue that P ≠ NP.

The paper applies formal logic and set-theoretic arguments to the definitions of P and NP, attempting to show that the two classes are fundamentally different by analyzing the structural properties of polynomial-time verification versus polynomial-time computation. The core argument relies on informal logical assertions about decidability and computational bounds that are not grounded in rigorous complexity-theoretic formalism.

## Directory Structure

The attempt is organized so the reconstructed source and the formal work stay separate:

- `original/` - English reconstruction of the paper and source notes
- `original/ORIGINAL.md` - Markdown reconstruction of the paper's argument
- `proof/` - Forward formalization of the paper's claimed reasoning
- `refutation/` - Formal refutation of the argument

The root-level `ORIGINAL.md` is retained as a compatibility mirror, but the
`original/` directory is the preferred location for the reconstructed source.

## Main Argument

### The Approach

The paper uses formal logic reasoning to argue:

1. **Definitions via Logic**: The authors reformulate P and NP using propositional and predicate logic, defining P as the class of problems decidable by deterministic Turing machines in polynomial time and NP as problems where solutions are verifiable in polynomial time.

2. **Asymmetry Claim**: The central argument is that there is a fundamental logical asymmetry between *verifying* a solution (NP) and *finding* a solution (P), and that this asymmetry can be captured by formal logic to show the classes are distinct.

3. **Non-constructive Argument**: The paper argues that no polynomial-time algorithm can systematically find solutions for all NP problems because the formal logical structure of NP-complete problems requires non-deterministic "guessing."

4. **Conclusion**: From these logical arguments, the paper concludes that P ≠ NP.

### Key Claims

1. **Claim 1**: The formal logical characterization of NP requires an existential quantifier over an exponential search space, which no deterministic polynomial-time algorithm can simulate.
2. **Claim 2**: The asymmetry between ∃ (existential) and ∀ (universal) quantifiers in the formal description of NP and P respectively implies P ≠ NP.
3. **Claim 3**: Formal logic reasoning alone is sufficient to establish the separation.

## The Error

### Fundamental Flaw: Logical Asymmetry Does Not Imply Complexity Separation

The paper commits several fundamental errors:

**The Core Error**: The observation that NP uses existential quantifiers while P uses universal/bounded quantifiers is well-known and does not by itself prove separation. The question of P vs NP is precisely *whether* this apparent logical asymmetry translates into an actual computational separation.

**Why This Is Wrong**:

1. **Descriptive Complexity Does Not Immediately Separate Classes**: While it is true (by Fagin's theorem, 1974) that NP equals the class of problems expressible in existential second-order logic (∃SO), this descriptive characterization does not itself prove P ≠ NP. The fact that P can be characterized in first-order logic with a least fixed point operator (FO + LFP) does not immediately separate it from ∃SO without additional combinatorial or diagonalization arguments.

2. **The Quantifier Complexity Fallacy**: Asserting that "existential quantifiers cannot be eliminated by polynomial-time algorithms" is essentially a restatement of the P ≠ NP conjecture itself, not a proof. The paper does not show *why* no polynomial-time algorithm can perform the required simulation—it merely asserts it.

3. **Known Barriers Ignored**: Any valid proof of P ≠ NP must overcome three known barriers:
   - **Relativization** (Baker-Gill-Solovay, 1975): Proofs using only oracle-independent formal logic arguments relativize and thus cannot separate P from NP.
   - **Natural Proofs** (Razborov-Rudich, 1997): "Natural" combinatorial arguments cannot separate P from NP unless certain cryptographic assumptions fail.
   - **Algebrization** (Aaronson-Wigderson, 2009): Extensions of relativization using algebraic techniques also cannot separate the classes.
   The paper's formal logic approach falls squarely within the relativization barrier.

4. **Circular Reasoning**: The argument that "NP requires guessing, therefore NP ≠ P" assumes the conclusion. Every known polynomial-time algorithm can in principle simulate non-deterministic guessing on the instances where guessing happens to be correct. The paper does not rule out such algorithms.

5. **Insufficient Formalism**: The paper's use of formal logic is informal at the meta-level. The step from "NP is defined with existential quantifiers" to "P ≠ NP" requires a formal proof of a complexity lower bound, which the paper does not provide.

### Specific Technical Errors

1. **Confusing Logical Description with Computational Power**: Describing NP in terms of ∃ quantifiers and P in terms of bounded quantifiers captures their *definitions*, not the difficulty of separating them. This is like saying "integers are countable, reals are uncountable, therefore they are different"—correct conclusion, but the logical description step is trivial; the hard part (Cantor's diagonal argument) is not present.

2. **No Circuit Lower Bounds**: A proof of P ≠ NP requires showing that some NP problem requires super-polynomial circuit complexity. Formal logic arguments about quantifier structure do not provide circuit lower bounds.

3. **Failure on Restricted Cases**: The argument, if correct, would apply equally to PSPACE vs NP, or to BPP vs P. But these separations are also open problems. The paper provides no explanation for why it proves specifically P ≠ NP and not also these other separations.

4. **No Explicit Hard Instance**: A complete proof of P ≠ NP would need to exhibit a language L in NP and show that no polynomial-time algorithm decides L. The paper never provides such a language or algorithmic lower bound.

### The Core Logical Error

```
INCORRECT REASONING (Wen & Lin):
1. NP is defined using existential quantifiers (∃)
2. P is defined using only polynomial-time bounded computations
3. ∃ quantifiers are "inherently" non-polynomial
4. Therefore P ≠ NP

CORRECT UNDERSTANDING:
1. NP is defined using existential quantifiers — TRUE
2. P is defined using polynomial-time computations — TRUE
3. Whether ∃ quantifiers over polynomial certificates can be
   "eliminated" by polynomial-time computation is EXACTLY the
   P vs NP question — this step is not justified
4. Therefore the conclusion does not follow from the premises
```

## Broader Context

### Why Formal Logic Alone Cannot Settle P vs NP

The P vs NP problem sits at the intersection of computational complexity and mathematical logic. While logic provides tools for *characterizing* complexity classes (descriptive complexity theory), logic alone cannot *separate* them without additional combinatorial or algebraic arguments because:

1. **Logical Theories Are Incomplete** (Gödel): First-order logic theories strong enough to reason about arithmetic are incomplete. Formal logic cannot decide all mathematical truths.

2. **Relativization Barrier**: Any proof technique that works "in all oracle models" cannot separate P from NP. Formal logic reasoning—which does not use specific properties of concrete computation—is precisely such a technique.

3. **What Is Actually Required**: A proof of P ≠ NP requires one of:
   - Super-polynomial circuit lower bounds for a specific NP problem
   - A diagonalization argument that is "non-relativizing" (not destroyed by adding an oracle)
   - An algebraic or combinatorial argument that explicitly uses the structure of Boolean circuits

### The IIGSS Journal Context

The paper appeared in "Scientific Inquiry," a journal of the International Institute for General Systems Studies (IIGSS). This journal focuses on general systems theory and interdisciplinary research rather than theoretical computer science. The paper appears not to have undergone rigorous peer review by complexity theorists, which may explain why the fundamental barriers were not addressed.

## Formalization Goals

In this directory, we formalize:

1. **The Formal Logic Approach**: How the paper characterizes P and NP using logical quantifiers.
2. **The Asymmetry Claim**: The paper's argument that ∃ vs. ∀ quantifiers imply P ≠ NP.
3. **The Refutation**: Why logical characterization does not imply separation, and why the relativization barrier blocks this approach.

The formalization demonstrates that:
- The logical characterizations of P and NP are correct descriptions, not proofs of separation.
- The inference from "different logical descriptions" to "different classes" is unjustified.
- The argument falls within the relativization barrier.

## References

### Primary Source

- **Original Paper**: Wen, B. & Lin, Y. (2010). "THE ANSWER TO THE P/NP PROBLEM IS P≠NP!"
  - Published in: Scientific Inquiry - A Journal of the IIGSS, Vol. 11, No. 2, December 2010
  - Available at: http://www.iigss.net/Scientific-Inquiry/Dec2010/table.htm
  - Note: Original paper may no longer be freely accessible online

- **Reconstruction**: [`original/README.md`](original/README.md) and [`original/ORIGINAL.md`](original/ORIGINAL.md)
  - Canonical English reconstruction and source notes for this attempt

### Context

- **Woeginger's List**: Entry #70
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Brought to Woeginger's attention by Jeffrey Yi-Lin Forrest

### Complexity Theory Background

- **Baker-Gill-Solovay** (1975): Relativization barrier — oracle separation of P and NP in both directions
- **Fagin's Theorem** (1974): NP = ∃SO (existential second-order logic) — descriptive characterization of NP
- **Immerman-Vardi Theorem** (1982): P = FO + LFP on ordered structures — descriptive characterization of P
- **Razborov-Rudich** (1997): Natural proofs barrier
- **Aaronson-Wigderson** (2009): Algebrization barrier

## Key Lessons

1. **Description ≠ Separation**: Describing two classes in different logical languages does not prove they contain different problems.
2. **Quantifier Asymmetry Is Known**: The ∃ vs. deterministic-computation asymmetry is precisely the P vs NP conjecture, not a proof of it.
3. **Barriers Must Be Addressed**: Any P ≠ NP proof must explain how it overcomes relativization, natural proofs, and algebrization barriers.
4. **Peer Review Matters**: Papers claiming to solve major open problems require expert review by specialists in theoretical computer science.
5. **Logic Tools Are Not Enough**: Formal logic provides a language for describing complexity classes but additional combinatorial/algebraic arguments are needed to separate them.

## See Also

- [P vs NP Framework](../../p_eq_np/) - General framework for evaluating P vs NP claims
- [Repository README](../../../README.md) - Overview of the P vs NP problem
