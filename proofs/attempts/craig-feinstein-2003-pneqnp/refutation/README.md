# Craig Alan Feinstein (2003-04) - Refutation

## Why the Proof Fails

Feinstein's 2003-04 P≠NP attempt was based on a **restricted computational model** approach. The proof claimed:

1. NP-complete problems require exponential time in the restricted model
2. This lower bound transfers to general Turing machine computation
3. Therefore, P ≠ NP

The proof fails at **Step 2**: the transfer principle is FALSE.

## The Core Error

### The Invalid Transfer Principle

Feinstein claimed:

> If a problem requires exponential time in my restricted model, then it requires exponential time in general computation.

This is **logically invalid** because:

1. **Restricted models forbid certain techniques**: By definition, a restricted model limits what operations algorithms can use

2. **General computation has more tools**: Turing machines can use techniques unavailable in the restricted model

3. **Lower bounds don't transfer**: A problem being hard WITHOUT technique X doesn't mean it's hard WITH technique X

### Analogy: Sorting

Consider the comparison-based sorting lower bound:
- **In the comparison-based model**: Sorting requires Ω(n log n) comparisons
- **In general computation**: Radix sort achieves O(n) time using non-comparison operations

The comparison lower bound is **valid** but only applies to comparison-based algorithms. It doesn't imply that ALL sorting algorithms require Ω(n log n) time.

Feinstein made an analogous error: his restricted model lower bound was valid within that model, but couldn't be transferred to general computation.

## The Counterexample

According to Woeginger's list, Feinstein withdrew his paper after a **counterexample** was found. While the specific counterexample is not publicly documented (since the paper was withdrawn), the pattern is clear:

A counterexample algorithm would:
1. Use operations available in general Turing machines
2. But NOT available in Feinstein's restricted model
3. Solve the NP-complete problem in polynomial time

This directly contradicts the transfer principle and invalidates the proof.

## The Dilemma of Restricted Model Approaches

For any restricted model approach to prove P ≠ NP, one faces a fundamental dilemma:

### Case 1: The Restricted Model is Genuinely Weaker

If the restricted model forbids techniques available in general computation:
- Lower bounds in the model are CONDITIONAL
- They only apply to algorithms restricted to the model's operations
- The transfer principle FAILS
- The proof is INVALID

### Case 2: The Restricted Model Exactly Captures P

If the restricted model perfectly captures polynomial-time computation:
- Proving exponential lower bounds in this model
- Is exactly as hard as proving P ≠ NP directly
- No simplification is achieved
- The approach provides no advantage

There is no middle ground that makes restricted model approaches viable for resolving P vs NP.

## Formal Refutation

The formalizations in this directory (`lean/` and `rocq/`) demonstrate:

1. **`transfer_principle_fails`**: The transfer principle is false; there exist problems hard in restricted models but easy in general

2. **`claim_gap`**: The gap between what Feinstein's restricted model shows and what he claimed

3. **`counterexample_invalidates_transfer`**: How a counterexample algorithm contradicts the transfer principle

## Historical Note

Feinstein responsibly withdrew the paper upon discovering the flaw. This demonstrates proper scientific conduct: acknowledging when a claimed proof contains a fundamental error.

## References

- Woeginger's P vs NP page, Entry #11: "withdrawn after counterexample"
- Similar pattern seen in many other P vs NP attempts using restricted models
