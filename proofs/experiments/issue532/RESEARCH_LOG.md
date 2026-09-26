# Issue 532: twenty paired idea checks

This is a ranked queue of **research directions**, not a ranking of numerical
probabilities. Priority reflects how directly a successful *uniform,
unrestricted* theorem could bear on P versus NP, and whether its first proof
obligation can be stated precisely. Each row links to an independent Lean 4
file and Rocq file. Both prove the same small statement without `sorry`,
`Admitted`, or new axioms.

The files are **finite diagnostic models**. A successful check establishes only
the displayed finite claim. A counterexample rejects the stated shortcut, not
every possible method in that research area. No file proves P = NP or P ≠ NP.
In particular, checking a fixed input size gives no asymptotic running-time
bound or circuit lower bound.

| Rank | Direction and test | Observed result | Next proof obligation |
| --- | --- | --- | --- |
| 1 | **Exact SAT algorithm** ([Lean](lean/Idea01.lean), [Rocq](rocq/Idea01.v)): enumerate four assignments of a two-variable formula. | **Works at size two:** the search finds a witness. | Give a uniform SAT decider and prove correctness and a polynomial bound for all formula sizes. |
| 2 | **Certificate search** ([Lean](lean/Idea02.lean), [Rocq](rocq/Idea02.v)): one rejected certificate coexists with a valid one. | **Shortcut refuted:** a failed trial cannot certify unsatisfiability. | Prove a sound, complete search procedure for all instances; account for search cost. |
| 3 | **Verifier formalization** ([Lean](lean/Idea03.lean), [Rocq](rocq/Idea03.v)): a tiny conjunction verifier accepts only matching witnesses. | **Works in the toy model:** soundness holds for every pair of Booleans. | Formalize certificates, instance encodings, and time bounds for a genuine NP-complete language. |
| 4 | **Constraint propagation** ([Lean](lean/Idea04.lean), [Rocq](rocq/Idea04.v)): an odd XOR triangle has no global assignment. | **Pairwise-to-global shortcut refuted:** every edge is individually satisfiable, yet their conjunction is not. | Identify a restricted constraint class with a proved local-to-global theorem, or find a globally sound rule for arbitrary SAT. |
| 5 | **Greedy optimization** ([Lean](lean/Idea05.lean), [Rocq](rocq/Idea05.v)): a cheap first step leads to cost 11; a costlier first step leads to 3. | **Universal greedy claim refuted** by a concrete two-path cost model. | Prove an exchange invariant on a specified problem class; show how it would apply to an NP-complete instance. |
| 6 | **Local search and potential functions** ([Lean](lean/Idea06.lean), [Rocq](rocq/Idea06.v)): state 0 beats its neighbor 1, but state 2 beats state 0. | **Local-equals-global shortcut refuted.** | Find a potential or neighborhood for which every local optimum is globally optimal, with polynomial convergence and unrestricted coverage. |
| 7 | **Lossless compression** ([Lean](lean/Idea07.lean), [Rocq](rocq/Idea07.v)): dropping one bit maps distinct inputs to the same code. | **Naive compression refuted:** this encoder cannot preserve exact answers to every predicate. | Define the decoder, information retained, and computation cost; prove an exact representation theorem for the target language. |
| 8 | **Program induction from finite examples** ([Lean](lean/Idea08.lean), [Rocq](rocq/Idea08.v)): two functions agree on the observed input and disagree on another. | **Unrestricted generalization shortcut refuted.** | State the hypothesis class and prove a sample-to-global theorem under explicit assumptions. |
| 9 | **Description length versus running time** ([Lean](lean/Idea09.lean), [Rocq](rocq/Idea09.v)): the shorter toy program uses more steps. | **Length-implies-speed shortcut refuted** in this cost model. | Define a machine and prove a relationship, if any, between optimal description length and time for the intended task. |
| 10 | **Restricted circuit lower bounds** ([Lean](lean/Idea10.lean), [Rocq](rocq/Idea10.v)): negation reverses Boolean order. | **Monotone-only coverage refuted:** negation lies outside the monotone fragment. | Extend any restricted lower bound to unrestricted polynomial-size circuits, or prove a reduction that preserves the restriction. |
| 11 | **LP or SDP relaxations** ([Lean](lean/Idea11.lean), [Rocq](rocq/Idea11.v)): an intermediate relaxed value has smaller cost than either permitted integer value. | **Automatic integrality shortcut refuted.** | Prove integrality or sound exact rounding for the chosen encoding of a hard problem. |
| 12 | **Reduction verification** ([Lean](lean/Idea12.lean), [Rocq](rocq/Idea12.v)): a constant map changes a no-instance to a yes-instance. | **This reduction refuted** on one input. | Prove yes/no preservation, polynomial construction cost, and size bounds for every input. |
| 13 | **Approximation algorithms** ([Lean](lean/Idea13.lean), [Rocq](rocq/Idea13.v)): cost 4 is within factor two of 3 but is not optimal. | **Approximate-equals-exact shortcut refuted.** | Establish a gap reduction or exact recovery theorem that converts the claimed approximation to a decision result. |
| 14 | **Randomized search** ([Lean](lean/Idea14.lean), [Rocq](rocq/Idea14.v)): one seed succeeds and another fails. | **Observed-success-implies-guarantee shortcut refuted.** | Specify error probability, independent randomness, runtime, and whether the target conclusion requires derandomization. |
| 15 | **Circuit depth versus size** ([Lean](lean/Idea15.lean), [Rocq](rocq/Idea15.v)): equal-size toy shapes have different depths. | **Size-determines-depth shortcut refuted** in the simple shape model. | Define gate semantics and fan-in; relate uniform circuit depth and size to the desired complexity class. |
| 16 | **Diagonalization** ([Lean](lean/Idea16.lean), [Rocq](rocq/Idea16.v)): a Boolean function differs from two enumerated functions on their indexed inputs. | **Works for a finite list.** The diagonal itself remains a tiny Boolean function. | Formalize a uniform machine enumeration, resource bounds, and a nonrelativizing step that places the diagonal language in NP while excluding P. |
| 17 | **Enumeration accounting** ([Lean](lean/Idea17.lean), [Rocq](rocq/Idea17.v)): two Boolean variables have four explicit assignments. | **Count verified at size two.** | Prove a general cost bound for the proposed search or a valid shortcut; do not infer a lower bound from enumeration alone. |
| 18 | **Structural restrictions** ([Lean](lean/Idea18.lean), [Rocq](rocq/Idea18.v)): a restricted disjunction is always true, while the unrestricted family contains false. | **Easy-subclass-to-general shortcut refuted.** | Show the restriction still encodes every instance of a suitable NP-complete problem, or label the result as a special-case algorithm. |
| 19 | **Advice and nonuniformity** ([Lean](lean/Idea19.lean), [Rocq](rocq/Idea19.v)): input-dependent advice makes a solver trivial. | **Works only because the hint contains the answer.** | Restrict advice to depend on input *length* and bound its size; prove any transfer to uniform computation separately. |
| 20 | **Parallel and physical cost models** ([Lean](lean/Idea20.lean), [Rocq](rocq/Idea20.v)): independent tasks take a max, dependent tasks retain a sum. | **Toy scheduling check passes.** | Specify a computational model, bounded processors and precision, and a uniform simulation theorem before comparing complexity classes. |

## Failed attempts used as filters

The repository's [common-errors index](../../attempts/COMMON_ERRORS.md)
catalogues earlier attempts. In particular, its sections on assumed lower
bounds and hidden exponential work motivate rows 1, 2, and 17; local versus
global consistency motivates rows 4–6; counting and compression mistakes
motivate rows 7–9; relaxation and invalid reductions motivate rows 11–12;
special-case and heuristic claims motivate rows 13–14 and 18. Those earlier
attempts are examples of obligations to check, not evidence that every
direction above is impossible.

## Reproduction and evidence

Run `python3 experiments/issue532/generate.py` from the repository root to
regenerate all forty files. Then run `lake build` and the Rocq verification
command used by `.github/workflows/verification.yml`:

```sh
find proofs/experiments/issue532/rocq -name '*.v' -type f -print0 |
  while IFS= read -r -d '' file; do rocq compile "$file" || exit 1; done
```

The Lean and Rocq theorems are checked independently. Their names are aligned
by number, and each file is standalone so it can be removed or expanded as a
research direction progresses. Future work should replace these toy models
with explicit encodings, cost semantics, and general theorems while keeping
counterexamples and failed approaches in the log.

## Verification log (2026-09-26)

- All 20 new Lean files compiled individually with Lean 4.33.1.
- All 20 new Rocq files compiled individually with Rocq 9.2.
- The complete Rocq sweep compiled all 208 `.v` files under `proofs/`.
- `lake build` completed with 211 jobs after repairing the existing
  `contradictory_is_unsat` proof in the Maknickas 2011 refutation. The proof now
  uses the two concrete unit clauses to derive the contradiction.
- The latest [main-branch verification run](https://github.com/konard/p-vs-np/actions/runs/36211672580)
  had failed at `MaknickasRefutation.lean:108` with two unsolved goals; its
  Rocq job passed. The PR's earlier green run only checked the changed
  `.gitkeep` file, so both formal jobs were skipped.
