# Doron Zeilberger (2009) - P=NP via Subset Sum Algorithm (April Fool's Joke)

**Attempt ID**: 52 (from Woeginger's list)
**Author**: Doron Zeilberger
**Year**: 2009
**Date**: April 1, 2009
**Claim**: P=NP
**Paper**: [P=NP](http://www.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pnp.pdf)
**Status**: Intentional April Fool's Joke

## Summary

On April 1, 2009, mathematician Doron Zeilberger posted a paper claiming to prove P=NP by presenting a polynomial-time algorithm for the Subset Sum problem. The paper described a rigorous interval analysis approach involving the translation of Subset Sum into integral evaluation, requiring the solution of over 10,000 linear programming problems with 100,000+ variables each.

**Critical Caveat**: This was explicitly an April Fool's Day joke. Zeilberger later clarified that "the 'proof' itself is complete gibberish (and of course, intentionally so)," though he noted the paper contained "some valid general statements about humans."

## Main Argument (As Presented in the Joke Paper)

### The Subset Sum Problem

**Definition**: Given a set of integers and a target sum, determine whether any subset of the integers adds up to the target.

**Known Status**:
- NP-complete problem
- One of Karp's 21 NP-complete problems
- No polynomial-time algorithm is known (assuming P≠NP)

### The "Approach"

The paper claimed to solve Subset Sum in polynomial time through:

1. **Translation to Integral Evaluation**: Converting the discrete Subset Sum problem into a continuous integral evaluation problem
2. **Rigorous Interval Analysis**: Using rigorous mathematical analysis (not floating-point arithmetic) to evaluate these integrals
3. **Linear Programming**: Solving over 10,000 linear programming problems, each with more than 100,000 variables
4. **Claimed Polynomial Time**: Despite the massive computational requirements, claiming this could be done in polynomial time

### Key "Technical" Claims

The paper purported to:
- Represent subset sum decisions as definite integral evaluations
- Use interval arithmetic to rigorously bound these integrals
- Reduce the integral evaluation to a large collection of linear programming problems
- Solve all these LP problems efficiently enough to achieve polynomial time overall

## The "Error" (Why It's Nonsense)

### It's an Intentional Joke

The most important "error" is that **this was never meant to be a serious attempt**. Zeilberger himself stated:

> "the 'proof' itself is complete gibberish (and of course, intentionally so)"

The paper was posted on April 1st as an April Fool's Day joke, satirizing:
- The numerous incorrect P vs NP proofs that appear regularly
- The tendency to use overly complex mathematical machinery
- The gap between rigorous mathematics and computational feasibility

### Why the "Approach" Doesn't Work (From a Technical Perspective)

Even if we analyze the joke approach seriously, several obvious issues emerge:

#### 1. **Computational Complexity Ignored**

The paper claims to solve "over 10,000 linear programming problems with 100,000+ variables each." While each individual LP can be solved in polynomial time, the critical questions are:
- How many LP problems are needed? (Is it polynomial in the input size?)
- How large are the LPs? (The number of variables might itself be exponential in the input)
- What is the total complexity when combining all steps?

The paper hand-waves these questions away, which is the joke.

#### 2. **No Actual Algorithm**

The paper doesn't provide a concrete, verifiable algorithm that can be implemented and tested. Instead, it offers vague descriptions of "translating" the problem and "using rigorous methods."

A real proof would need to:
- Specify the exact translation from Subset Sum to integrals
- Prove this translation is computable in polynomial time
- Prove the integral evaluation method works correctly
- Analyze the total complexity rigorously

#### 3. **Reduction Goes the Wrong Way**

Even if we could solve integrals via LP (which is questionable), the critical step is:
- How do we encode Subset Sum as an integral in polynomial size?
- If the encoding requires exponential precision or exponential-sized LP problems, then the polynomial-time claim fails

The paper doesn't address this, because it's intentional nonsense.

#### 4. **The Joke's Real Target**

The paper satirizes several common mistakes in failed P vs NP attempts:
- **Unverifiable complexity claims**: Stating "polynomial time" without rigorous analysis
- **Overcomplicated machinery**: Using advanced mathematics (integrals, interval analysis) when the core complexity issue remains unaddressed
- **Missing the forest for the trees**: Focusing on fancy techniques while ignoring the exponential barrier

## Historical Context and Significance

### Why This Matters for P vs NP

While this is a joke, it serves an important purpose:

1. **Educational**: It teaches researchers and students to be skeptical of grand claims
2. **Satire**: It highlights the patterns in incorrect proofs
3. **Community Service**: It demonstrates what a non-proof looks like, helping people recognize similar patterns in serious (but incorrect) attempts

### Zeilberger's Intent

Zeilberger has made several contributions to mathematics and is known for:
- His work in combinatorics and computer algebra
- His philosophical writings about mathematics and proof
- His sense of humor and willingness to engage with mathematical culture

The April Fool's paper fits his style of using humor to make serious points about how mathematics is done and communicated.

### Reception

The paper was:
- **Immediately recognized** as a joke by most experts (posted April 1st was a strong hint)
- **Added to Woeginger's list** as entry #52, where it serves as a reminder not to take every claim seriously
- **Still occasionally cited** by people who don't realize it's a joke, demonstrating the importance of checking sources

## Formalization Goals

Despite this being a joke, we can still formalize some interesting aspects:

1. **The Subset Sum Problem**: Formally define the problem and its NP-completeness
2. **What P=NP Would Mean**: Formalize the claim that a polynomial-time algorithm for Subset Sum would imply P=NP
3. **Complexity Analysis Principles**: Formalize why "solving many LP problems" doesn't automatically give polynomial time
4. **The Reduction Barrier**: Formalize why reducing Subset Sum to another problem requires analyzing the reduction's complexity

Our formalization demonstrates:
- The Subset Sum problem is well-defined
- Any claimed polynomial-time algorithm must analyze total complexity, not just per-step complexity
- The gap between "intuitively polynomial" and "rigorously proven polynomial"

## Structure

- `paper/` - Contains reference to the original April Fool's paper
- `coq/` - Coq formalization of Subset Sum and complexity analysis
- `lean/` - Lean 4 formalization with similar structure
- `isabelle/` - Isabelle/HOL formalization

Each formalization will:
- Define the Subset Sum problem formally
- Define what "polynomial time" means
- Show that solving NP-complete problems requires careful complexity analysis
- Demonstrate the importance of rigorous proof

## References

### Primary Source

- **Original Paper**: Zeilberger, D. (2009). "P=NP"
  - Original URL: http://www.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pnp.pdf
  - Current URL: https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pnp.pdf
  - **Date**: April 1, 2009 (April Fool's Day)

### Author's Clarification

- Zeilberger explicitly stated this was "complete gibberish (and of course, intentionally so)"
- The paper was meant as satire, not a serious mathematical claim

### Context

- **Woeginger's List**: Entry #52
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Listed as an April Fool's Joke
- **Subset Sum Problem**: Karp, R. M. (1972). "Reducibility among combinatorial problems"

## Key Lessons

1. **Check the Date**: Papers posted on April 1st should be viewed with suspicion
2. **Check the Author's Intent**: Sometimes mathematicians post jokes to make points about their field
3. **Verify Claims**: Even serious-looking papers can be satire
4. **Understand the Target**: This joke satirizes common mistakes in P vs NP attempts:
   - Claiming polynomial time without rigorous analysis
   - Using complex machinery to hide complexity issues
   - Confusing "elegant approach" with "correct proof"
5. **The Value of Humor**: Jokes can be educational and help clarify what good proofs look like

## Note on Formalization

While this is a joke paper, the formalization is serious and demonstrates:
- How to properly define complexity classes
- How to analyze algorithm complexity rigorously
- Why vague claims about "polynomial time" are insufficient
- The importance of analyzing total complexity, not just individual steps

In some sense, formalizing this "joke proof" teaches us more about what a real proof would require than many serious (but flawed) attempts do.

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Subset Sum Problem](../../problems/subset_sum/) - Formal definition of the problem
- [Complexity Theory Basics](../../complexity/) - Foundations of computational complexity
- [Repository README](../../../README.md) - Overview of the P vs NP problem
