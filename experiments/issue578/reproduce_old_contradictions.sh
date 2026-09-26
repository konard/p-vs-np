#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
baseline=c4a7803d3f5f589b30a6ff2affba3ec087384c30
base_path=proofs/attempts/sergey-gubin-2010-peqnp/refutation

git -C "$repo_root" show "$baseline:$base_path/lean/GubinRefutation.lean" > "$scratch/BaselineLean.lean"
cat >> "$scratch/BaselineLean.lean" <<'LEAN'

theorem audit_gubin_asymmetry_false : False := by
  let g : DirectedGraph := ⟨0, fun _ _ => 0⟩
  exact gubin_formulation_is_asymmetric g
    ⟨⟨GubinLPFormulation g, True.intro⟩, rfl⟩

theorem audit_correspondence_is_true (g : DirectedGraph) : HasIntegralCorrespondence g := by
  constructor
  · intro _
    refine ⟨⟨⟨fun _ => 0⟩, True.intro⟩, ?_⟩
    intro i hi
    exact ⟨0, rfl⟩
  · intro _ _
    exact ⟨⟨fun i => i, True.intro⟩, True.intro⟩

theorem audit_gubin_refutation_false : False :=
  rizzi_refutation_2011 audit_correspondence_is_true
LEAN
lean "$scratch/BaselineLean.lean" > "$scratch/lean.log" 2>&1

git -C "$repo_root" show "$baseline:$base_path/rocq/GubinRefutation.v" > "$scratch/BaselineRocq.v"
cat >> "$scratch/BaselineRocq.v" <<'ROCQ'

Theorem audit_rocq_false : False.
Proof.
  destruct GubinRefutation.fractional_extreme_points_exist as [lp [ep H]].
  exact (H I).
Qed.
ROCQ
rocq compile "$scratch/BaselineRocq.v" > "$scratch/rocq.log" 2>&1

echo "Baseline Lean and Rocq both accepted proofs of False."
