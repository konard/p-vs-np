# Craig Alan Feinstein (2003-04) - Original Proof Idea

## The Claim

Craig Alan Feinstein claimed to prove **P ≠ NP** by establishing exponential lower bounds within a restricted computational model and then transferring these bounds to general Turing machine computation.

## Core Approach

### Step 1: Define a Restricted Computational Model

Feinstein defined a computational model with specific limitations on the operations that algorithms can perform. The exact details of this model are not fully preserved since the paper was withdrawn, but based on the pattern of similar attempts, it likely included:

- A limited set of allowed operations (e.g., only comparisons and basic arithmetic)
- Specific cost functions for each operation
- Constraints on how information can be accessed or transformed

### Step 2: Prove Lower Bounds in the Restricted Model

Within this restricted model, Feinstein attempted to show that NP-complete problems (such as SAT or the Hamiltonian Cycle problem) require exponential time. The argument likely followed the pattern:

1. Show that any algorithm in the restricted model must perform certain types of operations
2. Prove that these operations collectively require exponential time
3. Conclude that NP-complete problems require exponential time in the restricted model

### Step 3: Transfer to General Computation

The critical (and ultimately flawed) step was to argue that the exponential lower bound from the restricted model implies P ≠ NP for general Turing machines. This transfer principle was stated as:

> If a problem requires exponential time in the restricted model, then it requires exponential time in general computation.

### Step 4: Conclude P ≠ NP

From the transfer principle and the restricted model lower bound, Feinstein concluded that NP-complete problems require exponential time in general, hence P ≠ NP.

## Why This Approach Seemed Promising

The restricted model approach has intuitive appeal:

1. **Lower bounds are easier in restricted settings**: Many strong lower bounds are known for restricted models (decision trees, communication complexity, circuit complexity with restrictions)

2. **Captures "natural" algorithms**: Restricted models often capture the algorithms people actually use, making lower bounds in these settings seem meaningful

3. **Historical precedent**: Important results like the Ω(n log n) sorting lower bound use restricted models effectively

## The Fundamental Problem

However, this approach fails because:

1. **Restricted ≠ General**: Algorithms that are impossible in the restricted model may be trivial in general computation

2. **The transfer principle is false**: There is no valid way to transfer lower bounds from genuinely restricted models to unrestricted Turing machines

3. **The dilemma**: If the restricted model exactly captures polynomial-time computation, proving lower bounds is as hard as P vs NP itself. If it doesn't, the transfer fails.

## Historical Context

This attempt was part of Feinstein's broader work on unprovability claims, including:
- "The Riemann Hypothesis is Unprovable" (2003)
- "The Collatz 3n+1 Conjecture is Unprovable" (2003)

All of these papers shared the characteristic of making strong claims that, upon scrutiny, contained logical gaps or invalid reasoning steps.

## References

- Woeginger's P vs NP page, Entry #11
- arXiv submissions from 2003-04 (withdrawn)
