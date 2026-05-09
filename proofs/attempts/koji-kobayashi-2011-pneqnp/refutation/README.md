# Refutation

Kobayashi's 2011 attempt fails at the lower-bound steps. The paper gives
informal arguments about dependency materialization and machine bookkeeping, but
does not prove that every machine in the target class must follow those
strategies.

## Main Gap

For each separation, the paper argues that a named language cannot be solved by
a target class because a particular way of evaluating its dependencies exceeds
the target resource bound. That is not enough for a complexity-class lower
bound.

To prove `CHAOS notin AL`, for example, the paper would need to rule out every
alternating log-space algorithm for `CHAOS`, not just algorithms that explicitly
store the proposed cyclic dependency structure.

## Specific Failures

- `CHAOS notin AL`: cyclic dependency descriptions do not by themselves imply
  alternating log-space lower bounds.
- `ORDER notin NC`: sequential dependencies in one representation do not rule
  out all polylog-depth polynomial-size circuit families.
- `LAYER notin NL`: inability to store all combinations is not an NL lower
  bound unless every valid algorithm must store those combinations.
- `TWINE notin L`: counting many rotate paths does not prove deterministic
  log-space cannot decide the language.

The refutation files formalize this distinction by separating
"an algorithm with a chosen strategy fails" from "the language is not in the
class." The former does not imply the latter without a universality theorem.
