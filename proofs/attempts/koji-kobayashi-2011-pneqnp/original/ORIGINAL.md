# NP is not AL and P is not NC is not NL is not L

**Author:** Koji Kobayashi
**Year:** 2011
**Source:** arXiv:1110.0200
**Woeginger entry:** #78

This is a Markdown reconstruction of the English text and proof structure from
the arXiv source. Mathematical notation has been normalized where needed, but
the order of definitions and theorems follows the source.

## Overview

The paper claims that `NP` is not `AL` or `P`, that `P` is not `NC`, that `NC`
is not `NL`, and that `NL` is not `L`. The proposed criterion is a dependency
relation between subproblems: some problems need the results of other problems
before they can be computed. The paper claims that different dependency
structures separate complexity classes.

## Action Configurations and Virtual Turing Machines

The paper defines an **action configuration** as the part of a computation
configuration that decides the next transition. It includes the state, transition
function, head position, and tape symbol under the head.

It introduces:

- origin configuration,
- moving configuration,
- target configuration,
- affirm configuration,
- negate configuration,
- computation progress.

The paper calls the machine emulated by a universal Turing machine a **virtual
Turing machine** (`VTM`).

### Theorem: Log Space Records an Action Configuration

The paper claims that log space is necessary and sufficient to record an action
configuration: the state and transition function are fixed for a machine, the
head position uses logarithmic space, and the symbol under the head uses
constant space.

### Theorem: Branches Do Not Share Information

The paper claims that nondeterministic branches do not share information or
results. If two virtual machines share information and results, the paper says
they must be executed in the same branch.

### Theorem: Parallel VTMs Need Different Space

The paper claims that moving configurations executed in parallel must be
recorded in different space, and that VTMs needing each other's information must
execute in parallel.

## Machine Classes Used by the Paper

The paper uses:

- `NTM`: nondeterministic Turing machine for `NP`,
- `LATM`: logarithmic-space alternating Turing machine for `AL`,
- `LNTM`: logarithmic-space nondeterministic Turing machine for `NL`,
- `LDTM`: logarithmic-space deterministic Turing machine for `L`.

The paper restricts machines to binary tape alphabets, read-only input, writable
working memory, halting decision computations, and acyclic computation histories.

### Theorem: Structure of a Turing Machine

The paper says a deterministic machine has a singleton computation history, a
nondeterministic machine has a set of target configurations, and an alternating
machine has a family of sets of target configurations. It then treats these
structures as well-founded sets.

## Dependency Relations Between Problems

The paper defines a **variable problem** `P_i` and a **blocking problem** `P_j`
when the value of `P_i` is not confirmed until `P_j` is determined.

It writes:

- `P_j P_i` for computing `P_i` after `P_j`,
- `[P_i]` for a blocking problem of `P_i`,
- `[P_i] P_i` for computing `P_i` after `[P_i]`,
- `[P_i]^n` for iterated blocking problems.

It defines a **combined problem** `CP = {P_0, ..., P_{k-1}}` made from variable
problems, and truth assignments `V^0, V^1, ...`.

### Depend Relation and Depend Path

The paper writes `[P_i] -> P_i` for a dependency relation and
`[P_i]^n ~> P_i` for a transitive dependency path. A rotate path is a path from
`P_i` back to `P_i`.

### Theorem: Dependencies Force Shared Computation

The paper claims that if a universal machine cannot record the value of a
blocking problem, it must execute the blocking problem's VTM and the dependent
problem's VTM in parallel, and cannot record both in the same space.

### Theorem: Combined Problems as Sets

The paper treats a combined problem as a family of sets of truth assignments.
It then claims that combined problems with cyclic transitive dependencies are
not well-founded sets.

## Claim 1: `NP > AL = P`

The paper defines `CHAOS` as a combined problem where each element problem is in
`ClassNP` and each element problem's blocker is the whole combined problem.

It claims:

- `CHAOS in NP`: a nondeterministic machine guesses values and checks all
  element problems.
- `CHAOS notin AL`: an alternating log-space computation would have to create a
  well-founded structure, but `CHAOS` is allegedly not well-founded. Removing
  the cycle would require either `k = sqrt(n) > log(n)` space or
  `2^sqrt(n) > log(n)` space.
- Therefore `NP > AL = P`.

## Claim 2: `P > NC`

The paper defines `ORDER` as a linear dependency structure where each problem
depends on earlier problems.

It claims:

- `ORDER in P`: a universal machine computes problems sequentially.
- `ORDER notin NC`: parallel evaluation would need to assume exponentially many
  combinations or recompute sequential dependencies.
- Therefore `P > NC`.

## Claim 3: `NC > NL`

The paper defines `LAYER` as a layered dependency structure with length
`(log n)^m` and width `n / (log n)^m`.

It claims:

- `LAYER in NC`: antichain elements can be computed in parallel with
  polylogarithmic time.
- `LAYER notin NL`: a nondeterministic log-space machine cannot record all
  blocking values or all combinations along a rotating path.
- Therefore `NC > NL`.

## Claim 4: `NL > L`

The paper defines `TWINE` as a layered structure with blocking sets of size
`O(log n)` and rotate paths longer than a constant.

It claims:

- `TWINE in NL`: a nondeterministic log-space machine follows one dependency
  path at a time.
- `TWINE notin L`: a deterministic log-space machine cannot compare all
  satisfiability symmetries across all rotate paths.
- Therefore `NL > L`.

## Conclusion

The paper concludes:

```text
NP > AL = P > NC > NL > L
```

The formalization in this repository preserves the claimed dependencies and
marks the lower-bound steps as gaps, because the original text does not provide
machine-independent lower-bound proofs for the constructed languages.
