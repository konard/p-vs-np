# Core framework assumption audit (issue #570)

The Lean and Rocq P definitions now run a deterministic machine on a binary
input. A run starts with the input on a blank tape; accepting and rejecting
states halt. `InP` / `in_P` requires a polynomial bound on the number of steps
to one of those states, plus language membership exactly when that run accepts.
The constant-time witnesses for the empty and universal languages are proved,
not axiomatized. Run `python3 experiments/issue570/check_contradiction.py` to
check that the derivation of `False` in issue #570 is rejected by both provers.

The source files print their proof dependencies. Lean reports `propext` for
`empty_in_P` and `universal_in_P`, a standard Lean logical axiom, and no custom
axiom. Rocq reports both theorems as closed under the global context.

## Remaining assumptions and modeling gaps

| Item | Lean | Rocq | Audit |
| --- | --- | --- | --- |
| Polynomial bounds for constants, linear and quadratic functions | Proved | Proved | No extra assumption. |
| `P_subseteq_NP` | Axiom | Admitted | The current verifier is an arbitrary Boolean function. Its `polynomial_time_verifier` condition contains `True` in place of an execution-time proof, so this claim is not a certified complexity result. |
| `P_eq_or_neq_NP` | Axiom | Axiom | Classical excluded middle in the form used by this model; it does not decide which case holds. |
| Closure of P under complement | Axiom | Admitted | A machine-swapping construction and a proof about its runs are still needed. |
| Closure of NP under complement if P = NP | Axiom | Theorem using the two assumptions above | It inherits the unproved P-to-NP and P-complement claims. |
| Polynomial sums | Not in this Lean file | Admitted | Rocq arithmetic lemma; it is not used by the new membership proofs. |

`PolyTimeReduction` / `poly_time_reduction` compares `L1 x` with `L2 (f x)`
and requires a certified computation of `f`. A reduction program can be a
finite instruction-table machine from the shared machine model, a structural
bitwise-NOT scan, or the sequential composition of two such programs. Machine
output is the contiguous binary prefix of its final tape. Each machine
instruction, including halt, costs one step; the bitwise-NOT scan costs one
step per bit plus one final step. The certificates bound both runtime and
output length by expressions built from nonnegative constants, the input
length, addition, multiplication, and substitution. Composition adds running
times and substitutes the first output-size bound into the second bounds.
Lean and Rocq prove identity, composition, and the bitwise-NOT reduction
between the distinct singleton languages `{[true]}` and `{[false]}` without
new axioms. `experiments/issue573/` preserves the old arbitrary-Boolean-map
counterexample as a compile-rejection regression test.

`IsNPComplete` / `is_NP_complete` remains a candidate in this historical toy
framework because `InNP` / `in_NP` still has no machine runtime condition for
its Boolean verifier. The previous `NPComplete_in_P_implies_P_eq_NP` /
`NP_complete_in_P_implies_P_eq_NP` assertion remains removed. Restoring it
requires a verifier model and proof that composing a reduction program with a
decider preserves polynomial time in the same machine model.

The Turing-machine records still use unrestricted natural-valued transition
functions. Their state counts and alphabet sizes are metadata rather than
proved invariants, so the model should not yet be treated as a complete
formalization of standard P. The separate Agda framework also lacks a
machine-to-language correctness condition and is outside this Lean/Rocq fix.
