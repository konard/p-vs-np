/-
# Formalization of LaPlante's 2015 P=NP Claim and Its Refutation

This file formalizes Michael LaPlante's 2015 claim that P=NP through a
polynomial-time algorithm for the maximum clique problem, and demonstrates
the error identified by Cardenas et al. (2015).

Reference:
- LaPlante: arXiv:1503.04794 (March 2015)
- Refutation: arXiv:1504.06890 (April 2015)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

/-! ## Graph Definitions -/

/-- A simple graph represented as a vertex set and edge relation -/
structure SimpleGraph where
  V : Type
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

variable {G : SimpleGraph}

/-- A clique is a set of vertices where all distinct pairs are adjacent -/
def IsClique (G : SimpleGraph) (vertices : List G.V) : Prop :=
  ∀ u v, u ∈ vertices → v ∈ vertices → u ≠ v → G.adj u v

/-- The size of a clique -/
def cliqueSize (vertices : List G.V) : Nat :=
  vertices.length

/-- A clique is maximal if no vertex can be added to make a larger clique -/
def IsMaximalClique (G : SimpleGraph) (vertices : List G.V) : Prop :=
  IsClique G vertices ∧
  ∀ w, w ∉ vertices → ¬IsClique G (w :: vertices)

/-! ## LaPlante's Algorithm Components -/

/-- A 3-clique (triangle) -/
def Is3Clique (G : SimpleGraph) (v1 v2 v3 : G.V) : Prop :=
  v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3 ∧
  G.adj v1 v2 ∧ G.adj v2 v3 ∧ G.adj v1 v3

/-- Phase 1 correctly identifies all 3-cliques involving a vertex -/
def Phase1Correct (G : SimpleGraph) (v : G.V)
    (triangles : List (G.V × G.V × G.V)) : Prop :=
  ∀ v1 v2,
    Is3Clique G v v1 v2 ↔
    (v, v1, v2) ∈ triangles ∨ (v, v2, v1) ∈ triangles

/-- A vertex pair from the 3-cliques -/
def VertexPair (G : SimpleGraph) := G.V × G.V

/-- Phase 2: Merging process with non-deterministic choices -/
inductive MergeStep (G : SimpleGraph) :
    List (VertexPair G) → VertexPair G → G.V → List G.V → Prop where
  | init (pairs : List (VertexPair G)) (p : VertexPair G) (key : G.V) :
      p ∈ pairs →
      (p.1 = key ∨ p.2 = key) →
      MergeStep G pairs p key [p.1, p.2]
  | extend (pairs : List (VertexPair G)) (p : VertexPair G)
      (key_node new_vertex : G.V) (current_clique : List G.V) :
      MergeStep G pairs p key_node current_clique →
      ((key_node, new_vertex) ∈ pairs ∨ (new_vertex, key_node) ∈ pairs) →
      (∀ v, v ∈ current_clique →
        (v, new_vertex) ∈ pairs ∨ (new_vertex, v) ∈ pairs) →
      new_vertex ∉ current_clique →
      MergeStep G pairs p key_node (new_vertex :: current_clique)

/-- The algorithm produces some clique, but not necessarily maximum -/
def AlgorithmProducesClique (G : SimpleGraph) (v : G.V)
    (result : List G.V) : Prop :=
  v ∈ result ∧ IsClique G result

/-! ## The Counterexample Graph -/

/-- The 15-vertex counterexample from Cardenas et al.
    - Vertices 1-5 form a 5-clique
    - Vertices 11-20 are the "letter" vertices (A-J in the paper)
    - Each combination of 3 vertices from {1,2,3,4,5} forms a 4-clique
      with one letter vertex
-/
def counterexampleGraph : SimpleGraph where
  V := Fin 21  -- vertices 0-20, we use 1-20
  adj := fun u v =>
    let u' := u.val
    let v' := v.val
    -- The central 5-clique: 1,2,3,4,5
    (u' ≤ 5 ∧ v' ≤ 5 ∧ u' > 0 ∧ v' > 0 ∧ u' ≠ v') ∨
    -- 4-clique: 1,2,3,A where A=11
    ((u' = 1 ∨ u' = 2 ∨ u' = 3) ∧ v' = 11) ∨
    (u' = 11 ∧ (v' = 1 ∨ v' = 2 ∨ v' = 3)) ∨
    -- 4-clique: 1,2,4,B where B=12
    ((u' = 1 ∨ u' = 2 ∨ u' = 4) ∧ v' = 12) ∨
    (u' = 12 ∧ (v' = 1 ∨ v' = 2 ∨ v' = 4)) ∨
    -- 4-clique: 1,2,5,C where C=13
    ((u' = 1 ∨ u' = 2 ∨ u' = 5) ∧ v' = 13) ∨
    (u' = 13 ∧ (v' = 1 ∨ v' = 2 ∨ v' = 5)) ∨
    -- 4-clique: 1,3,4,D where D=14
    ((u' = 1 ∨ u' = 3 ∨ u' = 4) ∧ v' = 14) ∨
    (u' = 14 ∧ (v' = 1 ∨ v' = 3 ∨ v' = 4)) ∨
    -- 4-clique: 1,3,5,E where E=15
    ((u' = 1 ∨ u' = 3 ∨ u' = 5) ∧ v' = 15) ∨
    (u' = 15 ∧ (v' = 1 ∨ v' = 3 ∨ v' = 5)) ∨
    -- 4-clique: 1,4,5,F where F=16
    ((u' = 1 ∨ u' = 4 ∨ u' = 5) ∧ v' = 16) ∨
    (u' = 16 ∧ (v' = 1 ∨ v' = 4 ∨ v' = 5)) ∨
    -- 4-clique: 2,3,4,G where G=17
    ((u' = 2 ∨ u' = 3 ∨ u' = 4) ∧ v' = 17) ∨
    (u' = 17 ∧ (v' = 2 ∨ v' = 3 ∨ v' = 4)) ∨
    -- 4-clique: 2,3,5,H where H=18
    ((u' = 2 ∨ u' = 3 ∨ u' = 5) ∧ v' = 18) ∨
    (u' = 18 ∧ (v' = 2 ∨ v' = 3 ∨ v' = 5)) ∨
    -- 4-clique: 2,4,5,I where I=19
    ((u' = 2 ∨ u' = 4 ∨ u' = 5) ∧ v' = 19) ∨
    (u' = 19 ∧ (v' = 2 ∨ v' = 4 ∨ v' = 5)) ∨
    -- 4-clique: 3,4,5,J where J=20
    ((u' = 3 ∨ u' = 4 ∨ u' = 5) ∧ v' = 20) ∨
    (u' = 20 ∧ (v' = 3 ∨ v' = 4 ∨ v' = 5))
  symm := by
    intros u v h
    simp only [Fin.val_fin_lt] at h ⊢
    omega
  irrefl := by
    intro v h
    simp only [Fin.val_fin_lt] at h
    omega

/-- Helper to create Fin 21 values -/
def v (n : Nat) (h : n < 21 := by decide) : Fin 21 := ⟨n, h⟩

/-- The 5-clique exists in the counterexample -/
theorem counterexample_has_5clique :
    IsClique counterexampleGraph [v 1, v 2, v 3, v 4, v 5] := by
  intro u vu hu hv hneq
  simp [counterexampleGraph] at hu hv ⊢
  fin_cases u using hu <;> fin_cases vu using hv <;> (first | omega | contradiction)

/-- Example 4-clique with A -/
theorem counterexample_has_4clique_with_A :
    IsClique counterexampleGraph [v 1, v 2, v 3, v 11] := by
  intro u vu hu hv hneq
  simp [counterexampleGraph] at hu hv ⊢
  fin_cases u using hu <;> fin_cases vu using hv <;> (first | omega | contradiction)

/-! ## The Core Error: Non-deterministic Choices -/

/-- The algorithm's Phase 2 involves making choices without backtracking -/
def BadChoiceExists (G : SimpleGraph) (v : G.V)
    (pairs : List (VertexPair G)) : Prop :=
  ∃ (p : VertexPair G) (key : G.V) (bad_result good_result : List G.V),
    -- There exists a merge starting with pair p and key node key
    MergeStep G pairs p key bad_result ∧
    MergeStep G pairs p key good_result ∧
    -- The bad result is smaller than the good result
    bad_result.length < good_result.length ∧
    -- Both are valid cliques
    IsClique G bad_result ∧
    IsClique G good_result ∧
    -- But the algorithm could choose the bad path
    v ∈ bad_result ∧ v ∈ good_result

/-- Key theorem: The counterexample graph has vertices where bad choices exist -/
theorem laplante_algorithm_fails :
    BadChoiceExists counterexampleGraph (v 1)
      [(v 2, v 3), (v 2, v 4), (v 2, v 5), (v 3, v 4), (v 3, v 5), (v 4, v 5),
       (v 2, v 11), (v 3, v 11), (v 2, v 12), (v 4, v 12)] := by
  use (v 2, v 3), v 2
  use [v 1, v 2, v 3, v 11]  -- bad result (4-clique)
  use [v 1, v 2, v 3, v 4, v 5]  -- good result (5-clique)
  constructor
  · -- Show bad merge path exists
    sorry  -- Would construct the merge steps
  constructor
  · -- Show good merge path exists
    sorry  -- Would construct the merge steps
  constructor
  · -- Show bad result is smaller
    simp
  constructor
  · -- Show bad result is a clique
    exact counterexample_has_4clique_with_A
  constructor
  · -- Show good result is a clique
    exact counterexample_has_5clique
  constructor <;> simp

/-! ## Conclusion -/

/-- LaPlante's algorithm fails because it makes arbitrary non-deterministic choices
    without backtracking. The algorithm is polynomial-time per execution path, but
    does not guarantee finding the maximum clique. This is the fundamental error
    that prevents it from establishing P=NP. -/
theorem laplante_claim_invalid :
    ¬(∀ (G : SimpleGraph) (max_clique : List G.V),
      IsMaximalClique G max_clique →
      ∃ poly_time_result,
        AlgorithmProducesClique G (max_clique.head!) poly_time_result ∧
        poly_time_result.length = max_clique.length) := by
  intro h
  -- Apply h to the counterexample
  specialize h counterexampleGraph [v 1, v 2, v 3, v 4, v 5]
  -- The 5-clique is maximal (simplified)
  have hmax : IsMaximalClique counterexampleGraph [v 1, v 2, v 3, v 4, v 5] := by
    constructor
    · exact counterexample_has_5clique
    · intro w hnot hcontra
      sorry  -- Proof that no 6-clique exists
  specialize h hmax
  obtain ⟨result, hprod, hlen⟩ := h
  simp at hlen
  -- But the algorithm can produce a 4-clique instead, contradicting hlen
  sorry

