# Refutation: Holcomb 2011

This directory contains formal refutations of the specific claims made in Holcomb's
2011 P≠NP proof attempt.

## Contents

- `lean/HolcombRefutation.lean` - Lean 4 refutation
- `rocq/HolcombRefutation.v` - Rocq refutation

## What These Refutations Demonstrate

Since the "stochastic answer" concept is undefined, we cannot directly refute the
specific claim. Instead, the refutations:

1. **Show that every proposed interpretation fails**: Each concrete interpretation
   of "stochastic answer" either (a) does not separate P from NP, or (b) is not
   a valid property of decision problems

2. **Show that the proof structure is hollow**: Without a definition, the proof
   reduces to assuming what it wants to prove (the axioms are equivalent to
   assuming P ≠ NP in disguise)

3. **Demonstrate non-determinism ≠ randomness**: The NP definition uses existential
   quantification (∃), not probabilistic computation

4. **Show that uniform random answers don't separate P from NP**: Even if we define
   "stochastic" as "answers are uniformly distributed over YES/NO," this doesn't
   separate P from NP (many P problems have uniformly distributed answers over
   random inputs)

## The Refutation Arguments

### Refutation 1: HasManyWitnesses Does Not Separate P from NP

The first interpretation — "stochastic = has many witnesses" — fails because:

- Problems in P can have exponentially many solutions
  (e.g., "Is x ≥ 0?" — infinitely many witnesses)
- Problems in NP can have zero witnesses
  (e.g., unsatisfiable formulas have no satisfying assignment)

**Formally**: We exhibit a P problem with many witnesses, contradicting the claim
that HasManyWitnesses separates P from NP.

### Refutation 2: Decision Problems Have Deterministic Answers

The claim that NP-hard problems have "stochastic" or "random" answers is incoherent:

- For any fixed input x, x ∈ SAT or x ∉ SAT — there is no probability here
- The answer is determined by whether a satisfying assignment exists
- This is a mathematical fact about the formula, not a random outcome

**Formally**: We prove that for any decision problem, the answer to any specific
input is deterministic (a proposition that is either true or false).

### Refutation 3: Non-Determinism ≠ Randomness

NP uses existential quantification (∃):

```
x ∈ L  ⟺  ∃w. |w| ≤ poly(|x|) ∧ V(x, w) = 1
```

This is often stated as "non-deterministic polynomial time" but means:
- "There EXISTS a witness" — a logical statement
- NOT "randomly compute a witness" — a probabilistic statement

**Formally**: We distinguish the existential (∃) semantics of NP from the
probabilistic (Pr[]) semantics of BPP and RP.

### Refutation 4: The Axiom Circularity

The proof reduces to:
1. Assume StochasticAnswer separates P from NP (implicit in the axioms)
2. Therefore P ≠ NP

This is circular: the axioms `P_problems_not_stochastic` and
`some_NP_problem_is_stochastic` together directly imply P ≠ NP, regardless of
what StochasticAnswer means. The proof is therefore vacuously true from its
assumptions, not established by argument.

**Formally**: We show that the axiom `some_NP_problem_is_stochastic` combined
with `P_problems_not_stochastic` already encodes the assumption P ≠ NP.

## Key Complexity Theory Facts Used

1. **P ⊆ NP**: Standard inclusion
2. **NP defined by existential quantification**: Not by randomness
3. **BPP ≠ NP in general**: Randomized algorithms don't capture NP
4. **Decision problems have deterministic answers**: YES/NO, not probabilistic

## See Also

- [`../README.md`](../README.md) - Overview and error explanation
- [`../ORIGINAL.md`](../ORIGINAL.md) - Reconstructed description of original proof
- [`../proof/README.md`](../proof/README.md) - Forward proof formalization
