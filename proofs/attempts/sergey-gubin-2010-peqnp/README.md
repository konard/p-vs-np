# Sergey Gubin (2010) - P=NP via ATSP Polytope Formulation

**Attempt ID**: 66 (from Woeginger's list)
**Author**: Sergey Gubin
**Year**: 2010
**Claim**: P = NP
**Status**: Refuted

## Summary

In August 2010, Sergey Gubin published a paper titled "Complementary to Yannakakis' Theorem" claiming to prove P = NP. The work was presented at the 22nd MCCCC conference in Las Vegas in 2008 and later published in Volume 74 of *The Journal of Combinatorial Mathematics and Combinatorial Computing* (pages 313-321).

Gubin's approach was similar to other linear programming-based attempts: he claimed that the Asymmetric Traveling Salesman Problem (ATSP) polytope can be expressed by an asymmetric linear program of polynomial size. Since linear programming problems can be solved in polynomial time, and ATSP is NP-complete, this would imply P = NP.

## Main Argument

### The Approach

1. **ATSP Polytope**: Focus on the polytope associated with the Asymmetric Traveling Salesman Problem
2. **Polynomial-Sized LP**: Construct a linear programming formulation of polynomial size for the ATSP polytope
3. **Reference to Yannakakis**: Position the work as "complementary" to Yannakakis' theorem
4. **LP Solvability**: Leverage the fact that LP problems can be solved in polynomial time
5. **Claimed Implication**: If ATSP (an NP-complete problem) can be formulated and solved as polynomial-sized LP, then P = NP

### Connection to Yannakakis' Theorem

Yannakakis' theorem (1991) is a fundamental result in polyhedral combinatorics stating that the Traveling Salesman Problem polytope cannot be expressed via a symmetric extended formulation of polynomial size. This was a significant negative result showing limitations of certain approaches to solving NP-complete problems via linear programming.

Gubin's claim to be "complementary" to Yannakakis suggests:
- He may have attempted an **asymmetric** formulation (as opposed to symmetric)
- Or he may have claimed to work around Yannakakis' limitations in some other way

However, Yannakakis' result is a fundamental barrier, and circumventing it requires extraordinary proof.

## The Error

### Fundamental Issues with the Approach

**The Core Problem**: Like other LP-based P = NP attempts, this approach faces the fundamental gap between:
- **Linear Programming (LP)**: Can be solved in polynomial time, but solutions may be fractional
- **Integer Linear Programming (ILP)**: NP-complete, solutions are integral

**Why This Matters**:
1. The TSP/ATSP requires integer solutions (tours are discrete structures)
2. An LP formulation naturally allows fractional solutions
3. For the approach to work, the LP polytope must have a special property: all extreme points must be integral and correspond to valid tours
4. This property (integrality) is precisely what makes the problem hard

### Missing Proof of Integrality

The critical missing piece is a rigorous proof that:
- All extreme points of the proposed LP polytope are integral
- These integral extreme points correspond exactly to valid ATSP tours
- No fractional extreme points exist in the polytope

Without this proof, the LP formulation may:
- Have fractional optimal solutions that don't correspond to tours
- Fail to capture all valid tours as extreme points
- Not actually solve the ATSP problem

### Refutation

**Romeo Rizzi (2011)**: In January 2011, Romeo Rizzi published a refutation of Gubin's arguments. While specific details of the refutation are not widely available in online sources, this follows the pattern of other LP-based attempts:
- The claimed correspondence between LP solutions and combinatorial structures fails
- Counter-examples can be constructed
- The integrality property is not proven

## Historical Context

### Yannakakis' Theorem Background

**Yannakakis (1991)**: Showed that the TSP polytope has no symmetric polynomial-size extended formulation. This result:
- Closed off one natural approach to solving TSP via LP
- Established fundamental limits on polyhedral methods
- Is a cornerstone result in combinatorial optimization

### The LP vs ILP Gap

This is a well-understood barrier in complexity theory:
- **LP (Linear Programming)**: In P - solvable via ellipsoid method, interior point methods
- **ILP (Integer Linear Programming)**: NP-complete - fundamentally harder
- **The Gap**: Converting continuous optimization to discrete optimization is the hard part

Many attempted P = NP proofs try to bridge this gap by claiming:
- "My LP formulation has integral extreme points"
- "The polytope structure ensures integrality"
- "The formulation is 'complementary' to known limitations"

But proving such claims requires rigorous mathematical proof, which is typically where these attempts fail.

## Similar Attempts

### Related LP-Based P=NP Claims

1. **Moustapha Diaby (2004)**: Claimed polynomial-sized LP formulation of TSP
   - Refuted by Hofman (2006, 2025) with counter-examples
   - See: `proofs/attempts/moustapha-diaby-2004-peqnp/`

2. **Other ATSP/TSP LP attempts**: Multiple researchers have tried similar approaches
   - All face the same fundamental issue: the LP/ILP gap
   - Counter-examples typically show non-integral extreme points

### Why These Approaches Are Tempting

The strategy is appealing because:
- LP formulations of TSP/ATSP do exist
- LP can be solved efficiently
- The connection seems "almost there"
- Small variations (symmetric vs asymmetric, different constraints) seem like they might work

But the fundamental barrier remains: **integrality is hard**.

## Formalization Goals

In this directory, we formalize:

1. **The ATSP Problem**: Definition as an NP-complete problem
2. **LP Formulation Claims**: What it means to have a polynomial-sized LP for ATSP
3. **The Integrality Requirement**: The critical property needed for the argument to work
4. **Why This Would Imply P = NP**: The logical structure of the argument
5. **The Gap**: Where the proof fails (integrality not proven)
6. **The Barrier**: Connection to Yannakakis' theorem and fundamental limitations

The formalization demonstrates that:
- The argument structure is well-formed
- The critical step (proving integrality and correspondence) is non-trivial
- Without this proof, the argument fails
- This is a common pattern in failed P = NP attempts

## References

### Primary Sources

- **Original Paper**: Gubin, S. (2010). "Complementary to Yannakakis' Theorem"
  - *The Journal of Combinatorial Mathematics and Combinatorial Computing*, Volume 74, pages 313-321
  - Also appeared on arXiv: https://arxiv.org/abs/cs/0610042
  - Conference presentation: 22nd MCCCC conference, Las Vegas, 2008

### Refutations

- **Romeo Rizzi (2011)**: Refutation published in January 2011
  - Specific publication details not widely available
  - Listed in Woeginger's P vs NP page as refuting Gubin's claim

### Related Work

- **Yannakakis (1991)**: "Expressing combinatorial optimization problems by linear programs"
  - *Journal of Computer and System Sciences*, 43(3), 441-466
  - DOI: 10.1016/0022-0000(91)90024-Y
  - Fundamental result on limitations of symmetric LP formulations

- **Diaby (2004-2006)**: Similar LP-based TSP approach
  - arXiv:cs/0609005
  - http://www.business.uconn.edu/users/mdiaby/tsplp/

- **Hofman (2006)**: "Report on article: P=NP Linear programming formulation of the Traveling Salesman Problem"
  - arXiv:cs/0610125
  - Counter-examples to LP-based approaches

### Context

- **Woeginger's List**: Entry #66
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Comprehensive list of P vs NP attempts with status

## Key Lessons

1. **The LP/ILP Distinction**: The gap between continuous and discrete optimization is fundamental to computational complexity

2. **Integrality is Hard**: Proving that an LP polytope has integral extreme points is typically as hard as the original problem

3. **Yannakakis' Barrier**: Fundamental limitations exist on polyhedral approaches to NP-complete problems

4. **"Complementary" Doesn't Mean "Circumvents"**: Being complementary to a negative result doesn't automatically mean you've found a workaround

5. **Proof Obligations**: Claiming a formulation has special properties (like integrality) requires rigorous proof, not just construction

6. **Common Pattern**: Many P = NP attempts follow similar structures and fail at similar points

## Technical Details

### The ATSP Problem

The Asymmetric Traveling Salesman Problem:
- **Input**: A directed graph with edge weights
- **Question**: Find a minimum-weight Hamiltonian cycle
- **Asymmetry**: The weight from vertex i to j may differ from j to i

### Why ATSP vs TSP?

- **TSP**: Symmetric - edge weights are the same in both directions
- **ATSP**: Asymmetric - allows different weights for different directions
- **Complexity**: Both are NP-complete
- **Yannakakis' Result**: Applies to symmetric formulations
- **Gubin's Angle**: Focus on asymmetric formulations as potentially avoiding the barrier

However, asymmetry alone doesn't solve the fundamental integrality problem.

## See Also

- [Moustapha Diaby's TSP Attempt](../moustapha-diaby-2004-peqnp/) - Similar LP-based approach
- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Proof Experiments](../../experiments/) - Other experimental approaches
- [Repository README](../../../README.md) - Overview of the P vs NP problem
