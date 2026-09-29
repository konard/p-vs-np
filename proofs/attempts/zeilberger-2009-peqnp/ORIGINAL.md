# P=NP

**Author**: Doron Zeilberger
**Date**: April 1, 2009 (April Fool's Day)
**Status**: Intentional April Fool's Joke

## Original Paper

**Note**: This is an April Fool's Day joke paper. The author himself stated that "the 'proof' itself is complete gibberish (and of course, intentionally so)."

## Paper Content (Summary)

The paper claims to prove P=NP by providing a polynomial-time algorithm for the Subset Sum problem.

### Abstract (Paraphrased)

On April 1, 2009, Doron Zeilberger posted a paper titled "P=NP" claiming to solve the Subset Sum problem (an NP-complete problem) in polynomial time, thus proving P=NP.

### Main Claims

The paper describes an approach involving:

1. **Translation to Integral Evaluation**: Converting the discrete Subset Sum problem into a continuous integral evaluation problem
2. **Rigorous Interval Analysis**: Using rigorous mathematical analysis (not floating-point arithmetic) to evaluate these integrals
3. **Linear Programming**: Solving over 10,000 linear programming problems, each with more than 100,000 variables
4. **Claimed Polynomial Time**: Despite the massive computational requirements, claiming this could be done in polynomial time overall

### The "Algorithm"

The paper vaguely describes:
- Representing subset sum decisions as definite integral evaluations
- Using interval arithmetic to rigorously bound these integrals
- Reducing the integral evaluation to a large collection of linear programming problems
- Solving all these LP problems "efficiently enough" to achieve polynomial time

### Why It's Nonsense

1. **No actual algorithm**: The paper provides only vague descriptions without concrete, verifiable steps
2. **Complexity analysis missing**: Claims "polynomial time" without proving the number of LP problems or their sizes are polynomial in the input
3. **Intentional joke**: Posted on April 1st and explicitly acknowledged by the author as complete gibberish
4. **Satirical purpose**: Meant to parody common mistakes in failed P vs NP attempts:
   - Unverifiable complexity claims
   - Using overly complex mathematical machinery to hide lack of substance
   - Hand-waving away the exponential barrier

### Author's Statement

Zeilberger clarified: "the 'proof' itself is complete gibberish (and of course, intentionally so)," though he noted the paper contained "some valid general statements about humans."

## Educational Value

Despite being a joke, this paper teaches important lessons:

1. **Rigorous analysis required**: Claiming polynomial time requires proving polynomial bounds on ALL operations
2. **Total complexity matters**: If you solve K problems of time T(n) each, total is K × T(n). If K is exponential, so is total.
3. **Encoding size matters**: Reductions only help if encoding is efficient AND polynomial-sized
4. **Verification is key**: Extraordinary claims require extraordinary proof with every step verified
5. **Always check the date**: Especially on April 1st!

## Links

- **Current URL**: https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pnp.pdf
- **Original URL**: http://www.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pnp.pdf (redirects to current URL)

## Translation Notes

This document is in English. The original paper is also in English.
