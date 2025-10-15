# Experimental Proof Attempts

**Navigation:** [↑ Proofs](../) | [↑ P ≠ NP Proofs](../p_not_equal_np/) | [Back to Repository Root](../../README.md)

---

## Overview

This directory contains rigorous experimental attempts to prove major results in complexity theory, primarily focusing on P vs NP. These are **not claimed proofs**, but rather:

- Serious explorations using state-of-the-art techniques
- Educational demonstrations of research methodology
- Documentation of barriers and why they prevent completion
- Formal verification of conditional results
- Templates for future research directions

**Key Principle:** Honesty and rigor. We clearly document what we attempt, what we achieve, what we cannot do, and why.

---

## Contents

### 1. P ≠ NP via Williams' Framework

#### [p_not_equal_np_proof_attempt.md](p_not_equal_np_proof_attempt.md)
**Comprehensive exploration using algorithm-to-lower-bound techniques**

**What it contains:**
- Full explanation of Williams' framework (2011 breakthrough)
- Attempted extension from ACC⁰ to TC⁰ and toward P/poly
- Detailed analysis of four major barriers encountered
- Conditional results and insights
- Roadmap for future research

**Key findings:**
- ✓ Williams' framework is mathematically sound and avoids known barriers
- ✓ Technique successfully proves NEXP ⊄ ACC⁰
- ✗ Cannot design fast enough SAT algorithms for TC⁰ (need 2^(n-n^δ), have 2^(n-O(log n)))
- ✗ Gap from TC⁰ to P/poly too large to bridge with current techniques
- ✗ Fundamental circular dependency for P vs NP (need fast NP algorithms to prove no fast NP algorithms)

**Educational value:** Demonstrates how modern techniques overcome relativization, natural proofs, and algebrization barriers, while clarifying precisely where we get stuck.

**Related:** [WilliamsFramework.lean](WilliamsFramework.lean) - Formal verification component

---

#### [WilliamsFramework.lean](WilliamsFramework.lean)
**Lean 4 formalization of Williams' technique**

**What it formalizes:**
```lean
-- Circuit complexity infrastructure
structure Circuit
structure CircuitClass
def ComputedBy (L : Language) (C : CircuitClass) : Prop

-- SAT algorithms and speedup
structure SATAlgorithm (C : CircuitClass)
def IsFastSATAlgorithm {C : CircuitClass} (alg : SATAlgorithm C) : Prop

-- Main theorem (axiomatized for components we don't have)
axiom williams_main_theorem (C : CircuitClass) (alg : SATAlgorithm C) :
  IsFastSATAlgorithm alg → ∃ (L : Language), L ∈ NEXP ∧ ¬(ComputedBy L C)

-- Our conditional result
theorem our_conditional_result :
  (∃ (alg : SATAlgorithm TC0), IsFastSATAlgorithm alg) →
  ∃ (L : Language), L ∈ NEXP ∧ ¬(ComputedBy L TC0)
```

**Purpose:**
- Demonstrates formal structure of Williams' approach
- Proves conditional results are correct (given assumptions)
- Provides infrastructure for circuit complexity in Lean
- Educational template for complexity theory formalization

**Status:** Compiles successfully in Lean 4. Uses axioms for unproven algorithmic components.

---

## What Blocks the Proof Attempt

### Primary Blocker: Algorithmic Barrier

**The core problem:** We cannot design fast enough SAT algorithms.

**Specifically for TC⁰ (threshold circuits):**
- **Need:** Algorithm running in time 2^(n - n^δ) for some δ > 0
- **Have:** At best 2^(n - O(log n)) for restricted variants
- **Gap:** Polynomial in the exponent (enormous difference)

**Why this matters:**
- Williams' diagonalization requires time budget 2^n (for NEXP)
- Must enumerate ~n^k circuits and test each for satisfiability
- Need speedup beyond 2^(n-O(log n)) to stay within budget
- Without fast SAT algorithm, diagonalization fails

**Why it's hard:**
- TC⁰ circuits are very expressive (compute majority, threshold functions)
- Less rigid structure than ACC⁰ (where Williams succeeded)
- Known algorithmic techniques (polynomial method, depth reduction) insufficient
- May require fundamentally new algorithmic paradigms

### Secondary Blocker: Complexity Gap

**The distance problem:** TC⁰ to P/poly is huge.

**Hierarchy:**
```
TC⁰ ⊂ TC ⊂ NC¹ ⊂ L ⊂ NL ⊂ NC ⊂ AC ⊂ P/poly
```

Each step requires:
- New SAT algorithm design
- Different structural properties to exploit
- Progressively stronger speedup requirements

**Current state:**
- Williams 2011: NEXP ⊄ ACC⁰ ✓
- Extending to TC⁰: No fast algorithm yet ✗
- Path to P/poly: Many more steps needed ✗

### Tertiary Blocker: Circular Dependency

**The fundamental limitation:** For P vs NP specifically, Williams' method hits a wall.

**The circularity:**
1. To prove P ≠ NP via Williams' method, need to show NP ⊄ P/poly
2. Showing NP ⊄ P/poly requires fast P/poly-SAT algorithm
3. But P/poly-SAT is itself NP-complete (or harder)
4. So we need fast algorithms for NP-complete problems...
5. ...to prove no fast algorithms for NP-complete problems exist!

**Resolution:**
- Technique works for NEXP vs circuit classes (NEXP problems likely harder than NP)
- May not work directly for NP vs P/poly
- Suggests hybrid approach or different final step needed

### Quaternary Blocker: Time Budget Constraints

**Diagonalization efficiency problem:**

**Time analysis:**
- NEXP machines: 2^n time budget
- Circuits to check: ~2^(n^k) possibilities (for size n^k)
- SAT checks needed: One per circuit
- Required speedup: Must complete all checks in 2^n time

**Math:**
```
Total time = (# circuits) × (time per SAT check)
           = 2^(n^k) × T_SAT

For this to work:
  2^(n^k) × T_SAT ≤ 2^n
  ⟹ T_SAT ≤ 2^(n - n^k)
  ⟹ Need VERY fast SAT algorithm
```

**Reality:** Current SAT algorithms nowhere near required speedup for stronger circuit classes.

---

## Would Coq Help?

### Short Answer: Not for the algorithmic barrier, yes for verification.

### What Coq Could Help With:

#### 1. **Formal Verification** ✓
- Port WilliamsFramework.lean to Coq
- Use richer library ecosystem (Mathcomp, Coq-std++)
- Leverage existing formalizations of complexity theory
- More mature proof automation in some areas

**Benefit:** Increased confidence in conditional results, better infrastructure

**Impact on proof:** None (we already know conditional results are correct)

#### 2. **Complete Formalization of Williams 2011** ✓
- Formalize the full NEXP ⊄ ACC⁰ proof
- Build comprehensive circuit complexity library
- Educational value for proof techniques

**Benefit:** Understanding and documentation

**Impact on proof:** Indirect (better understanding may inspire new approaches)

#### 3. **Extracting Algorithms** ✓
- Use Coq's extraction mechanism to generate verified SAT algorithms
- Ensure algorithmic correctness

**Benefit:** Correct implementation of any algorithms we design

**Impact on proof:** Helpful but doesn't solve the core problem (we still need to DESIGN fast algorithms)

### What Coq Cannot Help With:

#### 1. **Designing Fast SAT Algorithms** ✗
- This is a fundamental algorithmic research problem
- No proof assistant can automatically discover 2^(n-n^δ) SAT algorithms
- Requires mathematical insights not yet conceived
- Pure creativity and research, not formalization

#### 2. **Overcoming Fundamental Barriers** ✗
- Coq can verify proofs, not create new mathematical insights
- Circular dependency is real, not a formalization issue
- Complexity gaps exist in reality, not in our model

#### 3. **Replacing Human Ingenuity** ✗
- Williams' 2011 breakthrough required creative algorithm design
- Extending to TC⁰ requires similar breakthrough
- This is open research problem, not formalization challenge

### Recommendation:

**Yes, use Coq (or continue with Lean), but for the right reasons:**

1. **Use it to:** Formalize conditional results, build infrastructure, verify correctness
2. **Don't expect it to:** Solve the algorithmic barriers, design fast SAT algorithms, bypass fundamental limitations

**Analogy:**
- Proof assistant is like a rigorous notebook ensuring our math is correct
- But we still need to come up with the mathematical ideas to write in it
- Coq can verify Williams' technique works (given assumptions)
- Coq cannot tell us how to design faster SAT algorithms

**Best practice:**
- Formalize what we have in Coq for robustness
- Work on algorithmic research separately
- Use formalization to clarify exactly what algorithmic properties are needed
- This precision might indirectly inspire algorithmic approaches

---

## Other Approaches to Try

Given the barriers with Williams' framework, what else could we explore?

### 1. **Hybrid Approaches** (High Priority)

#### 1.1 Williams + Geometric Complexity Theory (GCT)
**Idea:** Combine algorithmic techniques with representation theory

**Approach:**
- Use Williams' framework for partial results (up to TC⁰ or TC)
- Apply GCT for final steps toward P/poly
- GCT uses different mathematical tools (representation theory, algebraic geometry)

**Potential:**
- Avoids circular dependency (GCT doesn't require fast SAT algorithms)
- Two barrier-avoiding techniques together
- Active research area

**Status:** Highly speculative, no clear path yet

**To explore:**
1. Study GCT literature (Mulmuley-Sohoni program)
2. Identify where Williams' results could feed into GCT framework
3. Formalize connection between circuit lower bounds and orbit closures

---

#### 1.2 Williams + Proof Complexity
**Idea:** Connect SAT algorithms to proof complexity lower bounds

**Approach:**
- SAT algorithms ↔ Short proofs (duality)
- Lower bounds on proof length ↔ Algorithm hardness
- Use proof complexity techniques for circuit classes

**Potential:**
- Different angle on same problem
- Rich mathematical structure
- Connection to automatability

**Status:** Theoretical connections known, practical application unclear

**To explore:**
1. Study resolution complexity for circuit formulas
2. Investigate cutting planes proofs for arithmetic circuits
3. Connect to bounded arithmetic

---

### 2. **Alternative Circuit Lower Bound Techniques** (Medium Priority)

#### 2.1 Approximation Method
**Idea:** Prove lower bounds for approximate computation

**Approach:**
- Show circuits cannot even approximate NP-hard functions well
- Easier than exact lower bounds
- Recent progress (Rossman, Håstad, etc.)

**Potential:**
- Side-steps some barriers
- Concrete progress possible

**Status:** Active research area with some successes

**To explore:**
1. Study approximation lower bounds for specific circuit classes
2. Connect to hardness of approximation results
3. Explore average-case complexity

---

#### 2.2 Monotone Circuit Lower Bounds
**Idea:** Prove lower bounds for restricted circuit models

**Approach:**
- Focus on monotone circuits (no negation gates)
- Known super-polynomial lower bounds for Clique, Perfect Matching
- Try to extend techniques

**Potential:**
- More tractable than general circuits
- Techniques might generalize

**Status:** Well-studied, some strong results

**To explore:**
1. Study Razborov's monotone lower bounds
2. Investigate recent extensions (Gálvez et al.)
3. Try to lift monotone lower bounds to general circuits

---

### 3. **Focus on Intermediate Results** (High Priority, Achievable)

#### 3.1 Improve TC⁰-SAT Algorithms
**Idea:** Push algorithmic frontier forward incrementally

**Approach:**
- Target: Any improvement beyond 2^(n - O(log n))
- Even 2^(n - (log n)^2) would be publishable
- Build on Williams' ACC⁰-SAT techniques

**Potential:**
- Concrete achievable goal
- Publishable even if not reaching 2^(n - n^δ)
- Incremental progress toward ultimate goal

**Status:** Active research problem, some recent work

**To explore:**
1. Study depth reduction for threshold circuits
2. Apply learning algorithms (PAC learning connections)
3. Random restrictions and simplification

**Concrete next steps:**
1. Implement Williams' ACC⁰-SAT algorithm
2. Attempt modifications for TC⁰ circuits
3. Experiment with depth reduction parameters
4. Test on concrete examples

---

#### 3.2 Extend Williams to TC (Unbounded Depth Threshold Circuits)
**Idea:** Target intermediate class between TC⁰ and P/poly

**Approach:**
- TC = Unbounded depth, polynomial size, threshold gates
- Strictly contains TC⁰
- May have exploitable structure

**Potential:**
- Significant result (NEXP ⊄ TC)
- Closer to P/poly than TC⁰
- Different algorithmic techniques may apply

**Status:** Open problem, natural next target

**To explore:**
1. Design SAT algorithms for small-depth TC circuits
2. Iterate depth reduction
3. Apply parallel algorithms techniques

---

### 4. **Meta-Complexity Approaches** (Medium Priority, Novel)

#### 4.1 Study MCSP (Minimum Circuit Size Problem)
**Idea:** Understand hardness of finding circuits

**Approach:**
- MCSP: Given function table, find smallest circuit
- Related to Williams' technique (SAT ↔ circuit finding)
- Prove MCSP is hard → Implications for lower bounds

**Potential:**
- Connects algorithm design to lower bounds
- Natural worst-case problem
- Recent interest in complexity community

**Status:** Active research area

**To explore:**
1. Study MCSP hardness results
2. Connect to Williams' framework
3. Investigate average-case variants

---

#### 4.2 Natural Proofs Barrier Revisited
**Idea:** Try to constructively avoid natural proofs

**Approach:**
- Razborov-Rudich showed broad class of techniques fail
- But relies on cryptographic assumptions
- Can we exploit non-generic properties to avoid?

**Potential:**
- If crypto assumptions false, barrier vanishes
- Even if true, understanding helps

**Status:** Speculative

**To explore:**
1. Study natural proofs barrier in detail
2. Identify techniques that provably avoid it
3. Connect to Williams' method (already avoids it)

---

### 5. **Complete Formalization Projects** (High Priority, Achievable)

#### 5.1 Formalize Williams 2011 Completely
**Goal:** Full Lean/Coq proof of NEXP ⊄ ACC⁰

**Steps:**
1. Formalize ACC⁰ circuit model
2. Implement and verify Williams' ACC⁰-SAT algorithm
3. Formalize diagonalization argument
4. Connect all pieces

**Value:**
- Educational resource
- Infrastructure for circuit complexity
- Template for extensions
- Confidence in technique

**Feasibility:** Achievable with substantial effort (months of work)

---

#### 5.2 Build Circuit Complexity Library
**Goal:** Reusable Lean/Coq library for circuit lower bounds

**Components:**
- Circuit models (AC⁰, ACC⁰, TC⁰, NC, AC, P/poly)
- Standard results (Håstad switching lemma, depth reduction)
- Complexity classes (P, NP, PSPACE, NEXP)
- Lower bound techniques

**Value:**
- Enables future formalization work
- Educational tool
- Research infrastructure

**Feasibility:** Achievable, would benefit entire community

---

### 6. **Experimental/Computational Approaches** (Low Priority, Complementary)

#### 6.1 SAT Algorithm Experimentation
**Idea:** Implement and test SAT algorithms for circuit classes

**Approach:**
1. Implement Williams' ACC⁰-SAT algorithm
2. Test on benchmarks
3. Try modifications for TC⁰
4. Measure actual speedup

**Value:**
- Concrete data on algorithm performance
- May inspire theoretical improvements
- Educational value

**Feasibility:** Achievable with programming effort

---

#### 6.2 Circuit Lower Bound Databases
**Idea:** Catalog known lower bounds systematically

**Approach:**
- Database of circuit classes
- Known lower bounds for each
- Techniques used
- Barriers encountered

**Value:**
- Research resource
- Identifies gaps
- Educational tool

**Feasibility:** Achievable, would benefit community

---

## Recommended Priority Order

### Immediate (Next 1-2 Months):
1. **Improve TC⁰-SAT algorithms** - Concrete algorithmic work
2. **Complete formalization infrastructure** - Build Lean/Coq libraries
3. **Study hybrid approaches** - Literature review and exploration

### Near-Term (3-6 Months):
4. **Target intermediate results** - NEXP vs TC, improved algorithms
5. **Formalize Williams 2011 completely** - Full verification
6. **Explore proof complexity connections** - Alternative angle

### Medium-Term (6-12 Months):
7. **GCT integration attempts** - Long-term research direction
8. **MCSP and meta-complexity** - Novel approaches
9. **Approximation lower bounds** - Alternative targets

---

## Relationship to Repository Framework

These experiments connect to:

### Formal Verification Framework
- [proofs/p_not_equal_np/](../p_not_equal_np/) - Test Method 4 (Super-Polynomial Lower Bounds)
- [proofs/p_not_equal_np/lean/](../p_not_equal_np/lean/) - Lean infrastructure

### Strategy Documentation
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Strategy 3.1 (Algorithm-to-Lower-Bound)

### Core Documentation
- [P_VS_NP_TASK_DESCRIPTION.md](../../P_VS_NP_TASK_DESCRIPTION.md) - Problem background
- [TOOLS_AND_METHODOLOGIES.md](../../TOOLS_AND_METHODOLOGIES.md) - Available techniques

---

## How to Use This Directory

### For Students:
1. Read [p_not_equal_np_proof_attempt.md](p_not_equal_np_proof_attempt.md) to understand modern approaches
2. Study [WilliamsFramework.lean](WilliamsFramework.lean) for formal structure
3. Review barriers section above to understand current limitations

### For Researchers:
1. Identify which blocker you want to tackle
2. Choose approach from "Other Approaches to Try"
3. Use formalizations as starting point
4. Contribute back improvements and extensions

### For Contributors:
1. Follow same structure for new experiments
2. Be honest about limitations
3. Connect to existing framework
4. Update this README with new findings

---

## Contributing

To add a new experimental proof attempt:

1. Create markdown document with:
   - Background and motivation
   - Technical development
   - Barriers encountered
   - Insights gained
   - Future directions

2. Add formal verification component (Lean/Coq) if applicable

3. Update this README with:
   - Description of experiment
   - Status and findings
   - Connection to other work

4. Submit via pull request

---

## License

All content in this directory is provided under The Unlicense (see [../../LICENSE](../../LICENSE)).

---

## Acknowledgments

This work builds on:
- **Ryan Williams** (2011+): Algorithm-to-lower-bound breakthrough
- **50+ years** of complexity theory research
- **Razborov, Rudich, Aaronson, Wigderson, et al.**: Barrier results
- **Lean and Coq communities**: Formal verification infrastructure

---

**Navigation:** [↑ Proofs](../) | [Repository Root](../../README.md) | [Solution Strategies](../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md)
