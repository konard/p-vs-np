# Vladimir Romanov (2010) - P=NP via Compact Triplets Structures

**Attempt ID**: 67
**Author**: Vladimir F. Romanov
**Year**: 2010
**Claim**: P = NP
**Status**: Unsupported
**Source**: Woeginger's P-versus-NP list, entry #67; arXiv:1011.3944

## Summary

Vladimir Romanov's paper, "Non-Orthodox Combinatorial Models Based on
Discordant Structures", claims a polynomial-time method for 3-SAT. Since 3-SAT
is NP-complete, a correct deterministic polynomial-time algorithm for all 3-SAT
instances would imply P = NP.

The proposed method rewrites a 3-CNF formula as tabular formulas whose clauses
fit adjacent triples of variables. These tables are transformed into compact
triplets structures (CTS). For a general 3-CNF formula, Romanov decomposes the
formula into several CTS built over different variable permutations, called
discordant structures. A unification procedure and a system of hyperstructures
are then used to decide whether the discordant CTS have a joint satisfying set.

## Claimed Argument

1. Convert each suitable tabular formula into a CTS.
2. Decompose any 3-CNF formula into CTS over several variable permutations.
3. Build a hyperstructure system over the discordant CTS.
4. Use the systemic effective procedure (SEP) to form this hyperstructure system.
5. Claim that the original formula is satisfiable exactly when the SEP result is
   non-empty.
6. Bound the SEP running time by a polynomial, stated as `O(n^4 m)`.

The central claim is Theorem 2 of the paper: joint satisfying sets exist for the
CTS system if and only if SEP forms a non-empty system of hyperstructures.

## Error

The proof does not establish the sufficiency direction of Theorem 2. It shows how
the procedure propagates local compatibility constraints between adjacent triples
and same-name substructures, but it does not prove that every non-empty final
hyperstructure contains a globally consistent assignment satisfying all original
clauses.

This is the standard local-consistency gap in constraint satisfaction:

- local pair/triple compatibility can remain non-empty;
- projections and intersections can be mutually compatible in the maintained
  representation;
- nevertheless, no single global Boolean assignment may realize all constraints.

For 3-SAT, any polynomial-time algorithm based only on such a certificate must
prove a global soundness invariant: every non-empty SEP state must contain an
actual joint satisfying set. Romanov's induction assumes this invariant through
the "same-name intersection" and bijective-mapping language, but does not derive
it from the CTS operations.

## Formalization

The formalization records both the intended proof skeleton and the precise gap.

- `proof/lean/RomanovProof.lean` and `proof/rocq/RomanovProof.v` model the CTS,
  discordant structure, SEP, and the claimed implication from a non-empty SEP
  result to satisfiability.
- `refutation/lean/RomanovRefutation.lean` and
  `refutation/rocq/RomanovRefutation.v` isolate the missing global soundness
  invariant and show that local consistency alone is insufficient.

The formal files intentionally keep the disputed implication as `sorry`/`Admitted`.
The derived P = NP conclusion depends exactly on that unsupported step.

## References

- Romanov, V. F. "Non-Orthodox Combinatorial Models Based on Discordant
  Structures." arXiv:1011.3944v2, 2011.
- Woeginger's P-versus-NP page, entry #67:
  https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Cook, S. A. "The Complexity of Theorem-Proving Procedures." STOC 1971.
- Garey, M. R. and Johnson, D. S. *Computers and Intractability*, 1979.
