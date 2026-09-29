# Issue 587 Kardash 2-SAT regression

Before the fix, the Kardash refutation said that unit propagation and arc
consistency decide 2-SAT, credited that to Krom (1967), and recorded it in Lean
and Rocq as an assumption whose type was `True`. The two formulas from the
issue refute that explanation:

- `(x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y)` is unsatisfiable, but unit
  propagation from the empty assignment does nothing and arc consistency with
  one constraint per clause removes nothing.
- The Boolean triangle `x ≠ y, y ≠ z, z ≠ x` is arc-consistent with full
  domains but has no solution.

Files:

- `kardash_2sat.py` implements unit propagation, clause-wise arc consistency,
  the implication-graph strongly connected component test, and Kardash's pair
  cleaning (Definitions 3-15 of the paper). `python3 kardash_2sat.py` prints a
  summary, including a brute-force comparison on every 2-CNF over three
  variables.
- `test_kardash_2sat.py` keeps both counterexamples, checks that the SCC test
  and pair cleaning agree with brute force on 2-CNFs, and checks that the
  attempt's READMEs and proof files no longer make the old claim.
- `check.sh --lean` and `check.sh --rocq` build the refutation and print the
  axioms of the checked 2-SAT results (`Audit.lean`, `Audit.v.in`). Lean may
  use only `propext`, `Quot.sound` and `Classical.choice`; every Rocq result
  must be closed under the global context.

Run:

```bash
python3 -m unittest discover -s experiments/issue587 -p 'test_*.py' -v
bash experiments/issue587/check.sh --lean
bash experiments/issue587/check.sh --rocq
```

Before the fix the source checks in `SourceClaims` fail (22 subtests); the
behavioural tests pass on both sides, since they test the formulas rather
than the files. The Rocq audit has a `.v.in` suffix so the normal full-project
scan does not compile it on its own.
