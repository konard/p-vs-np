# Issue 532: forty paired idea checks

This is a queue of **research directions**, not a ranking of numerical
probabilities. The first twenty rows are finite diagnostics. The second twenty
isolate general proof steps and countermodels suggested by the first batch and
the repository's failed-attempt catalogue. Each row links to an independent
Lean 4 file and Rocq file. Both prove the same small statement without `sorry`,
`Admitted`, or new axioms.

The files establish only the statements displayed in the code. A
counterexample rejects the stated shortcut, not every method in that area.
General lemmas in the second batch are often *conditional*: the missing
hypothesis is the actual research problem. No file proves P = NP or P ≠ NP.
In particular, a fixed input size gives no asymptotic running-time bound or
circuit lower bound. Nor does a logical implication provide the polynomial
resource bounds absent from its assumptions.

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

## Second round: twenty more concrete routes

The most direct positive route is a uniform exact SAT algorithm with a proved
polynomial bound (21–22, 29). The most direct negative route is an unrestricted
lower bound with a correct simulation from every polynomial-time algorithm
(30). These are *targets*, not achieved results. The other rows test proposed
ingredients or expose a condition that an attempted transfer must satisfy.
The row number continues the first batch; it is not a probability estimate.

| No. | Candidate direction and paired check | Checked result | Missing theorem or decisive next test |
| --- | --- | --- | --- |
| 21 | **Exact SAT branching** ([Lean](lean/Idea21.lean), [Rocq](rocq/Idea21.v)): an existential Boolean branch is equivalent to its two cases. | General logical equivalence proved. | Find a sound rule that avoids exhaustive branching on unrestricted SAT and prove a uniform polynomial total cost. |
| 22 | **Decision-to-search self-reduction** ([Lean](lean/Idea22.lean), [Rocq](rocq/Idea22.v)): an *exact* decision answer selects a satisfiable branch. | Conditional selection lemma proved. | Supply an exact polynomial-time decider; count all adaptive oracle calls and reduction costs. |
| 23 | **Resolution-based SAT reasoning** ([Lean](lean/Idea23.lean), [Rocq](rocq/Idea23.v)): the resolvent follows from its parent clauses. | Soundness of one inference proved. | Establish polynomially bounded refutations for every unsatisfiable CNF, or explain why stronger reasoning escapes known size limits. |
| 24 | **Unit propagation** ([Lean](lean/Idea24.lean), [Rocq](rocq/Idea24.v)): a unit clause and a compatible clause imply the remaining literal. | Soundness proved. | Characterize a complete polynomial propagation rule for unrestricted SAT; a rule that works on a tractable fragment is insufficient. |
| 25 | **Decomposable constraints** ([Lean](lean/Idea25.lean), [Rocq](rocq/Idea25.v)): independent components have a product witness. | General decomposition lemma proved. | Find a polynomially computable decomposition for all hard instances, with bounded interfaces and exact witness reconstruction. |
| 26 | **Separator consistency** ([Lean](lean/Idea26.lean), [Rocq](rocq/Idea26.v)): separately satisfiable components can disagree on a shared bit. | Explicit countermodel proved. | Track all shared assignments and prove the resulting state space remains polynomial for the intended unrestricted family. |
| 27 | **Variable elimination** ([Lean](lean/Idea27.lean), [Rocq](rocq/Idea27.v)): existentially removing one Boolean variable preserves the two branches. | General equivalence proved. | Bound intermediate representation size and elimination order on every CNF, or prove a new compact exact representation. |
| 28 | **Definitional extensions** ([Lean](lean/Idea28.lean), [Rocq](rocq/Idea28.v)): an auxiliary variable with an equivalence constraint preserves satisfiability. | General equivalence proved. | Show that the extended encoding makes exact solving polynomial, including encoding and decoding cost. |
| 29 | **Reduction chain to SAT** ([Lean](lean/Idea29.lean), [Rocq](rocq/Idea29.v)): preservation and target correctness compose. | General conditional transfer proved. | Formalize an actual NP-complete reduction, input encodings, and polynomial time bounds for each composition. |
| 30 | **Unrestricted circuit lower bound** ([Lean](lean/Idea30.lean), [Rocq](rocq/Idea30.v)): lower bound plus uniform simulation and size bound excludes a fast algorithm. | General conditional contradiction proved. | Prove the lower bound for unrestricted circuits computing an explicit NP language and the quantitative machine-to-circuit simulation; audit [known barriers](#research-context). |
| 31 | **Length-wise advice** ([Lean](lean/Idea31.lean), [Rocq](rocq/Idea31.v)): a two-entry table stores any one-bit-input function. | Finite nonuniform representation proved. | Bound advice for every input length and distinguish a family of circuits from one uniformly constructible algorithm. |
| 32 | **Promise algorithms** ([Lean](lean/Idea32.lean), [Rocq](rocq/Idea32.v)): correctness on a promise leaves an outside input wrong. | Countermodel proved. | Prove the promise covers all reductions from the NP-complete target or give a total solver. |
| 33 | **Average-case transfer** ([Lean](lean/Idea33.lean), [Rocq](rocq/Idea33.v)): a function works on three of four points yet fails at one. | Countermodel proved. | Establish a worst-case-to-average-case reduction with a specified distribution and quantitative success bound. |
| 34 | **Adversarial lower-bound quantifiers** ([Lean](lean/Idea34.lean), [Rocq](rocq/Idea34.v)): every toy algorithm can have a hard input with no input hard for all algorithms. | Quantifier countermodel proved. | State hardness as `∀ algorithm, ∃ input` at arbitrarily large sizes, with the required resource bound; never silently exchange quantifiers. |
| 35 | **Exact compression** ([Lean](lean/Idea35.lean), [Rocq](rocq/Idea35.v)): a lossless encode/decode pair forces an injective encoder. | General theorem proved. | Specify the compressed object, decoder, exactness condition, and total construction/decoding cost; test for an information bottleneck. |
| 36 | **Exact relaxation and rounding** ([Lean](lean/Idea36.lean), [Rocq](rocq/Idea36.v)): a sound rounding map converts a relaxed witness into a discrete witness. | Conditional witness transfer proved. | Construct such a map for every relevant relaxed solution and prove polynomial bit complexity; otherwise document an integrality gap. |
| 37 | **Parameterized structure** ([Lean](lean/Idea37.lean), [Rocq](rocq/Idea37.v)): a monotone parameter cost is bounded when the parameter is bounded. | Conditional cost lemma proved. | Prove the parameter is uniformly bounded, or sufficiently small as a function of input length, on an NP-complete family. |
| 38 | **Relativization audit** ([Lean](lean/Idea38.lean), [Rocq](rocq/Idea38.v)): a property true in one abstract world need not hold in another. | Logical countermodel proved; **not** an oracle separation theorem. | State the candidate proof in an oracle model and identify its nonrelativizing step. |
| 39 | **Proof-system scope** ([Lean](lean/Idea39.lean), [Rocq](rocq/Idea39.v)): no proof in a weak system is consistent with a proof in a stronger one. | Countermodel to lower-bound transfer proved. | Establish a simulation from every relevant stronger proof/algorithm into the restricted system before drawing an unrestricted conclusion. |
| 40 | **Size-uniform invariant** ([Lean](lean/Idea40.lean), [Rocq](rocq/Idea40.v)): base case and a genuine induction step yield all input sizes. | General induction principle instantiated. | Prove a step that preserves correctness and a polynomial resource invariant for actual encoded instances; finite experiments cannot supply this step. |

### Research context

The official [P versus NP problem description](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
sets the asymptotic target. The [relativization result](https://doi.org/10.1137/0204037),
[natural proofs](https://www1.karlin.mff.cuni.cz/~krajicek/rr.pdf), and
[algebrization barrier](https://eccc.weizmann.ac.il/eccc-reports/2008/TR08-005/Paper.pdf)
inform the audit in row 30 and 38. Existing research on
[algorithms yielding circuit lower bounds](https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf)
motivates pursuing a precise algorithm-to-lower-bound transfer, but its
theorems do not by themselves separate P from NP. These papers are context
for the proposed routes; the paired files do not formalize their results.
The [resolution width–size tradeoff](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf)
and [extended-formulation lower bounds](https://arxiv.org/abs/1111.0837)
illustrate why rows 23 and 36 must specify the exact proof or optimization
system to which a bound applies.

## Failed attempts used as filters

The repository's [common-errors index](../../attempts/COMMON_ERRORS.md)
catalogues earlier attempts. In particular, its sections on assumed lower
bounds and hidden exponential work motivate rows 1, 2, and 17; local versus
global consistency motivates rows 4–6; counting and compression mistakes
motivate rows 7–9; relaxation and invalid reductions motivate rows 11–12;
special-case and heuristic claims motivate rows 13–14 and 18. Those earlier
attempts are examples of obligations to check, not evidence that every
direction above is impossible.

For the second batch, error families 1 and 16 motivate the unrestricted
simulation check in row 30; families 4 and 17 motivate reduction and encoding
accounting in row 29; families 2 and 7 motivate the representation and cost
checks in rows 27 and 35; families 3 and 5 motivate exact rounding in row 36;
and families 12–14 motivate the quantifier and barrier audits in rows 34 and
38–39.

## Reproduction and evidence

Run `python3 experiments/issue532/generate.py` from the repository root to
regenerate all eighty files. Then run `lake build` and the Rocq verification
command used by `.github/workflows/verification.yml`:

```sh
find proofs/experiments/issue532/rocq -name '*.v' -type f -print0 |
  while IFS= read -r -d '' file; do rocq compile "$file" || exit 1; done
```

The Lean and Rocq theorems are checked independently. Their names are aligned
by number, and each file is standalone so it can be removed or expanded as a
research direction progresses. Future work should extend these diagnostic
models and conditional lemmas with explicit encodings, cost semantics, and
substantive general theorems while keeping
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

## Second-round verification log (2026-09-26)

- All 20 new Lean files and all 20 new Rocq files compiled individually. The
  Rocq proof-system-scope script was corrected after its first compile exposed
  an over-eager `repeat split` tactic.
- `lake build` completed with 231 jobs for the full project.
- The full Rocq sweep compiled all 228 `.v` files under `proofs/`.
- `python3 -m py_compile` passed for both generator files. No second-round
  formal file uses `sorry`, `Admitted`, or an axiom.
