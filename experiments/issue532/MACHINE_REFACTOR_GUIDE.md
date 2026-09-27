# Rebasing the issue #532 ideas onto the shared machine model

This note records the conventions used to answer the PR #569 review ("four of
the six open obligations are provable outright, and none of the forty is
connected to `PEqualsNP`"). It applies to every file in
`proofs/experiments/issue532/{lean,rocq}` and every dossier in
`proofs/experiments/issue532/ideas`.

## The problem

The audit in `experiments/issue532_vacuity/REPORT.md` found that most "open
obligations" quantified over a free cost function (`time := 0` works), a free
predicate (`PolyTime`, `Efficient`, `NP`, `PPoly` chosen by the caller) or a
free class of algorithms. Such a definition is either provable or refutable
outright, so it is not an open problem, and a conditional theorem that takes it
as a hypothesis says nothing about P versus NP.

## The shared model

* `proofs/complexity/lean/Complexity.lean` (Rocq twin
  `proofs/complexity/rocq/Complexity.v`): `Word`, `Language`, `Machine`,
  `Run`, `Polynomial`, `ClassP`, `ClassNP`, `InP`, `InNP`, `PEqualsNP`,
  `PNotEqualsNP`.
* `proofs/experiments/issue532/lean/Machines.lean` (Rocq twin `Machines.v`):
  `DecidesWithin m p L`, `PolyDec`, `polyDec_iff_inP`, `inP_of_decidesWithin`;
  `Computes m f p` (a machine computes `f` within `p` steps), `PolyReduces`,
  `inP_of_reduces`; `DecidesOn m p Pr L` (correct on a promise) and
  `inP_of_promise_reduction`; `complement`, `inP_complement`, `InCoNP`,
  `NPEqualsCoNP`, `pNotEqualsNP_of_npNeCoNP`; `NPHard`, `NPComplete`,
  `npComplete_inP_iff`; `exists_language_not_in_family` (Cantor lemma for
  non-vacuity) with `encMachine`, `encMachinePoly`; CNF `Lit`/`Clause`/`CNF`,
  `evalCNF`, `Satisfiable`, `bruteForce_correct`, `encodeCNF`, `decode`,
  `decode_encode`; the language `SAT` with `sat_iff`, `sat_encode`;
  `SATInNP`, `SATHard`, `CookLevin`, `pEqualsNP_of_inP_sat`,
  `inP_sat_of_pEqualsNP`, `inP_sat_iff`.
* `proofs/experiments/issue532/lean/Circuits.lean`: NAND straight-line
  programs, `InPPoly`, `SuperpolyLowerBound`, `superpoly_iff_not_inPPoly`, the
  named known theorem `PSubsetPPoly`, and `pNotEqualsNP_of_superpoly_sat`.

## Rules

1. **An open obligation is a proposition about the shared model.** A definition
   whose docstring says "open obligation" imports `Machines` or `Circuits`,
   mentions a model name (`InP`, `DecidesWithin`, `Computes`, `SAT`,
   `InPPoly`, …) directly or through a definition of the same file, binds no
   free cost function (`t`, `time`, `cost`, `steps`) and binds no free
   predicate (`… → Prop`). `experiments/issue532/check_dossiers.py` enforces
   this. If the dossier verdict is "Developed to an open obligation", both the
   Lean and the Rocq file must label at least one definition this way.
2. **Time is a `Run` step count.** A decider is a `Complexity.Machine`; its
   cost is the `t` of `Run m (initial x) t b`. A computed map is
   `Computes m f p`.
3. **Every open obligation reaches the separation question.** Prove a
   conditional theorem from the obligation to `InP SAT`, `PEqualsNP` or
   `PNotEqualsNP`. Known theorems that are not mechanised (Cook–Levin halves,
   `PSubsetPPoly`, a machine construction such as seed enumeration) are named
   `def … : Prop` in the file or in the shared layer, documented as "Known
   theorem, not mechanised here" with a citation, and appear only as explicit
   hypotheses. They must be true statements.
4. **Non-vacuity.** Where feasible, prove that the obligation's class is not
   everything (for example `¬ ∀ L, InRP L` via `exists_language_not_in_family`),
   so the obligation is a statement about SAT and not a consequence of the
   definitions.
5. **Generic schemas stay, renamed.** A useful abstract statement over a free
   `PolyTime`/`time`/class is kept, renamed with the suffix `For` (for example
   `IsolationObligationFor`), and its docstring says "schema" and never "open
   obligation". The obligation is then its machine instance, and a second
   theorem instantiates the schema with the model.
6. **Nothing proved is removed.** Theorems that do not concern cost (counting,
   combinatorics, refutations) stay. Only the cost layer changes.
7. **No `sorry`, `axiom`, `admit`, `native_decide`, `opaque`; in Rocq no
   `Admitted`, `Axiom`, `Parameter`, `Hypothesis`, `Conjecture`.**
8. **Dossiers.** Update section 2 (formulation), section 3 (table of
   machine-checked names; each row must be declared in the Lean or the Rocq
   file, or the shared layer), section 6 (how far toward P vs NP, naming the
   known-theorem hypotheses), and the verdict. Remove caveats that described
   the old free-cost model; state honestly what remains (for example "the
   route needs `SATHard`, which is not mechanised").
