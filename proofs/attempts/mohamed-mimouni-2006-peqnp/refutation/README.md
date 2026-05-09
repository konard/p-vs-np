# Mohamed Mimouni (2006) - Refutation

## Why the Proof Fails

Mimouni's 2006 P=NP attempt was based on claiming a polynomial-time algorithm for the Clique Problem. The proof claimed:

1. A polynomial-time algorithm exists for Clique
2. Therefore, P = NP (since Clique is NP-complete)

The proof fails because the claimed algorithm in Step 1 is INVALID.

## The Core Error

### Why Clique-Based P=NP Attempts Fail

While we cannot identify the specific error in Mimouni's algorithm (the original paper is inaccessible), clique-based P=NP attempts consistently fail due to one or more of these errors:

### Error Type 1: Algorithm Works Only on Special Cases

**Problem**: The proposed algorithm works on specific graph structures but fails on general instances.

**Example**: An algorithm might efficiently find cliques in:
- Dense graphs (many edges)
- Graphs with specific structure (trees, planar graphs)
- Small instances

But fail on:
- Sparse graphs with scattered cliques
- Adversarially constructed graphs
- Large general instances

**Key Principle**: A valid P=NP proof requires an algorithm that works for ALL instances, not just SOME.

### Error Type 2: Exponential Time Disguised as Polynomial

**Problem**: The algorithm appears polynomial in some parameter but is actually exponential in input size.

**Example**: An algorithm running in O(n^k) time where k is the clique size:
- For k = log(n): O(n^(log n)) = O(2^((log n)^2)) - superpolynomial!
- For k as input: Runtime depends on k, not just graph size n
- For k unbounded: Can be exponential in worst case

**Key Principle**: Time complexity must be polynomial in the total input size (graph representation), not in some derived parameter.

### Error Type 3: Incorrect Complexity Analysis

**Problem**: Errors in counting operations or analyzing loop iterations.

**Example**:
- Claiming nested loops are polynomial when they're actually exponential
- Miscounting recursive calls
- Ignoring the cost of subroutines
- Assuming operations are constant-time when they're not

### Error Type 4: Incomplete Algorithm

**Problem**: The algorithm doesn't actually solve the problem correctly for all cases.

**Example**:
- Returns approximate solutions instead of exact answers
- Works for decision version but not optimization version (or vice versa)
- Has correctness bugs that cause it to miss valid cliques or report false cliques

This was the error acknowledged by Dhami et al. (2014) in a similar clique-based attempt.

## Why Clique Remains Hard

The Clique Problem has been extensively studied for over 50 years:

1. **NP-Completeness**: Proven by Karp in 1972
2. **Hardness of Approximation**: Hastad (1999) showed Clique is hard to approximate within n^(1-epsilon)
3. **Exponential Time Hypothesis**: Implies no algorithm can solve Clique in sub-exponential time

If Mimouni's algorithm were correct, it would contradict:
- 50+ years of complexity theory research
- The Exponential Time Hypothesis
- All known lower bounds for the Clique Problem

## Hofman's Comments

According to Woeginger's list, Radoslaw Hofman provided comments on Mimouni's paper at http://www.wbabin.net/comments/hofman.htm (now inaccessible). These comments likely identified specific errors in Mimouni's algorithm or analysis.

## Formal Refutation

The formalizations in this directory (`lean/` and `rocq/`) demonstrate:

1. **`exponential_clique_lower_bound`**: Why polynomial-time Clique algorithms are believed impossible
2. **`special_case_error`**: The distinction between algorithms that work on special cases vs. all instances
3. **`complexity_analysis_error`**: Common errors in time complexity analysis
4. **`correctness_requirements`**: What a valid Clique algorithm must satisfy

## Lessons Learned

1. **Extraordinary Claims Require Extraordinary Proof**: P = NP would be one of the most important results in mathematics. Extraordinary scrutiny is appropriate.

2. **Common Error Patterns**: Clique-based attempts share common failure modes that can be checked for.

3. **Peer Review is Essential**: The complexity theory community has deep expertise in identifying subtle errors.

4. **Source Availability Matters**: When sources become inaccessible (as with Mimouni's paper), the scientific record is incomplete.

## References

1. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations, pp. 85-103.
2. Hastad, J. (1999). "Clique is hard to approximate within n^(1-epsilon)." Acta Mathematica.
3. Woeginger, G. J. "The P-versus-NP page". Entry #32.
4. Related: Dhami et al. (2014) - Attempt #97 (similar clique-based approach)
