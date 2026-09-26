# Issue 578 reproduction

Run `bash experiments/issue578/reproduce_old_contradictions.sh` from a checkout
containing commit `c4a7803d3f5f589b30a6ff2affba3ec087384c30`. The script
loads the old source from that commit into a temporary directory and appends
the two Lean contradictions from the issue and the direct Rocq contradiction.
Success means both proof assistants accepted proofs of `False` from the old
assumptions. It does not change the current proof files.

The corrected audit is checked with:

```sh
python3 scripts/check_gubin_audit.py
lean proofs/attempts/sergey-gubin-2010-peqnp/refutation/lean/GubinRefutation.lean
rocq compile proofs/attempts/sergey-gubin-2010-peqnp/refutation/rocq/GubinRefutation.v
```

The audit theorem `asymmetry_does_not_imply_integrality` proves that an explicit
asymmetric two-variable LP has a fractional vertex.
`abstract_correspondence_can_fail` proves that a separate integral vertex
cannot encode a tour of a graph with no edges. Neither theorem is about
Gubin's specific LP.
