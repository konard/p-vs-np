# Issue 577 reproduction and regression check

At the audited base commit `c4a7803`, each snippet below compiled and proved `False` from one refutation axiom. Put a snippet immediately after the old Lean refutation source and run `lean` on the combined file:

```lean
theorem circularity_false : False :=
  PlotnikovRefutation.circular_reasoning_error True (fun h => h)

theorem unrelated_propositions_false : False :=
  (PlotnikovRefutation.algorithm_requires_conjecture False True).1 True.intro
```

The analogous old Rocq axioms also allowed contradictions:

```coq
Theorem circularity_false : False.
Proof.
  exact (circular_reasoning_error True (fun _ => eq_refl)).
Qed.

Theorem unrelated_propositions_false : False.
Proof.
  exact ((proj1 (algorithm_requires_conjecture False True)) I).
Qed.
```

The old `dilworth_computational_hardness` axiom separately denied that a cubic is polynomial under the local definition. The revised files prove `cubic_is_polynomial` instead.

Run the regression guard with:

```sh
python3 -m unittest discover -s experiments/issue577 -p 'test_*.py' -v
```

Both tests failed against the old files because the purported refutation used unproved axioms. They pass when the refutation files contain only definitions and proved theorems. The CI workflow runs this guard, then compiles the changed Lean and Rocq files.
