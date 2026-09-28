# Refutation

Meek's entry #46 argument fails at the reduction-theoretic level.

## Main Error

For languages `SAT` and `L`, the standard NP-completeness condition includes a
polynomial-time many-one reduction:

```
SAT <=p L
```

If `L` is decidable in polynomial time, SAT is decidable in polynomial time by:

1. map the SAT instance `x` to the `L` instance `f x`;
2. run the polynomial-time decider for `L`;
3. return the same yes/no answer.

This is the usual reason that one polynomial-time NP-complete decider implies
P = NP. Meek's requirement that the target algorithm directly expose a special
"underlying K-SAT" solution is not part of many-one reducibility.

## Special-Case Error

The paper also treats base conversion as NP-complete because it can be described
as a special form of Knapsack. That implication is invalid. A special case of an
NP-complete problem may be easy; 2-SAT is a standard easy restriction of SAT.

## Formal Files

- `lean/MeekKarpPostulatesRefutation.lean` models reduction composition and the
  special-case non sequitur.
- `rocq/MeekKarpPostulatesRefutation.v` records the same ideas in Rocq.
