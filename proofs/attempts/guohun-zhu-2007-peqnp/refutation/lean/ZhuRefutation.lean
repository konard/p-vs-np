import Init.Data.Nat.Lemmas

/-
  A finite projector graph witness for Zhu (2007), Lemma 4.

  The vertices of the Γ digraph are 0,...,5. From each pair {2i,2i+1}
  there are arcs to both vertices of the next pair (cyclically). Its projector
  graph has three independent C4 components. A bit in each component chooses
  one of its two labeled perfect matchings. The four different bit counts give
  four classes under the paper's code-permutation convention, exceeding n/2=3.

  This tests the counting step of Lemma 4. It does not prove that the paper's
  rank-greedy equations (10-11) fail on this graph or rule out another algorithm.
-/

namespace ZhuRefutation

abbrev Vertex := Fin 6
abbrev Code := Bool × Bool × Bool

def arc (u v : Vertex) : Bool :=
  v.val / 2 == (u.val / 2 + 1) % 3

-- The projector edge for an arc u → v has endpoints u⁺ and v⁻.
def projectorEdge (u v : Vertex) : Bool := arc u v

def leftComponent (u : Vertex) : Nat := u.val / 2
def rightComponent (v : Vertex) : Nat := (v.val / 2 + 2) % 3

-- Edge membership is exactly equality of component numbers. Each of the
-- three components has two left and two right vertices and all four edges.
theorem projector_component_edges :
    ∀ u v : Vertex,
      projectorEdge u v = true ↔ leftComponent u = rightComponent v := by
  decide

theorem projector_component_sizes :
    ∀ c : Fin 3,
      ((List.range 6).filter (fun u =>
        leftComponent ⟨u % 6, by omega⟩ == c.val)).length = 2 ∧
      ((List.range 6).filter (fun v =>
        rightComponent ⟨v % 6, by omega⟩ == c.val)).length = 2 := by
  decide

def matching (b : Code) (u : Vertex) : Vertex :=
  match u.val with
  | 0 => if b.1 then 3 else 2
  | 1 => if b.1 then 2 else 3
  | 2 => if b.2.1 then 5 else 4
  | 3 => if b.2.1 then 4 else 5
  | 4 => if b.2.2 then 1 else 0
  | _ => if b.2.2 then 0 else 1

def perfectMatching (m : Vertex → Vertex) : Prop :=
  (∀ u, projectorEdge u (m u) = true) ∧
  (∀ u v, m u = m v → u = v)

-- All 8 codes give bijective matchings of the actual projector graph.
theorem every_code_is_perfect : ∀ b : Code, perfectMatching (matching b) := by
  intro ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> unfold perfectMatching <;> decide

def reachesWithinThree (u v : Vertex) : Prop :=
  u = v ∨ arc u v = true ∨
  (∃ w, arc u w = true ∧ arc w v = true) ∨
  (∃ w z, arc u w = true ∧ arc w z = true ∧ arc z v = true)

-- Each vertex has two incoming and two outgoing arcs, and every vertex is
-- reachable from every other in at most three steps.
theorem degree_two_out : ∀ u : Vertex,
    ((List.range 6).filter (fun v => arc u ⟨v % 6, by omega⟩)).length = 2 := by
  decide

theorem degree_two_in : ∀ v : Vertex,
    ((List.range 6).filter (fun u => arc ⟨u % 6, by omega⟩ v)).length = 2 := by
  decide

theorem strongly_connected : ∀ u v : Vertex, reachesWithinThree u v := by
  unfold reachesWithinThree
  decide

-- Theorem 1(c3) claims at most n/4 C4 components, with n=|V(D)|.
-- The conjunction ties its failed bound to a valid Γ input and its projector.
theorem theorem1_c3_counterexample :
    (∀ u : Vertex,
      ((List.range 6).filter (fun v => arc u ⟨v % 6, by omega⟩)).length = 2) ∧
    (∀ v : Vertex,
      ((List.range 6).filter (fun u => arc ⟨u % 6, by omega⟩ v)).length = 2) ∧
    (∀ u v : Vertex, reachesWithinThree u v) ∧
    (∀ u v : Vertex,
      projectorEdge u v = true ↔ leftComponent u = rightComponent v) ∧
    (∀ c : Fin 3,
      ((List.range 6).filter (fun u =>
        leftComponent ⟨u % 6, by omega⟩ == c.val)).length = 2 ∧
      ((List.range 6).filter (fun v =>
        rightComponent ⟨v % 6, by omega⟩ == c.val)).length = 2) ∧
    3 > 6 / 4 := by
  exact ⟨degree_two_out, degree_two_in, strongly_connected,
    projector_component_edges, projector_component_sizes, by decide⟩

def codeWeight (b : Code) : Nat :=
  (if b.1 then 1 else 0) + (if b.2.1 then 1 else 0) +
    (if b.2.2 then 1 else 0)

-- Each weight denotes a distinct class under the code-permutation convention
-- used for the examples preceding Lemma 4. Arbitrary graph isomorphism is a
-- different quotient and is not established by this theorem.
theorem four_code_classes :
    codeWeight (false, false, false) = 0 ∧
    codeWeight (true, false, false) = 1 ∧
    codeWeight (true, true, false) = 2 ∧
    codeWeight (true, true, true) = 3 ∧
    3 < 4 := by
  decide

-- The n/2 bound is false for this Γ input under that convention.
theorem lemma4_code_bound_counterexample :
    ∃ b0 b1 b2 b3 : Code,
      perfectMatching (matching b0) ∧ perfectMatching (matching b1) ∧
      perfectMatching (matching b2) ∧ perfectMatching (matching b3) ∧
      codeWeight b0 = 0 ∧ codeWeight b1 = 1 ∧
      codeWeight b2 = 2 ∧ codeWeight b3 = 3 ∧
      6 / 2 < 4 := by
  refine ⟨(false, false, false), (true, false, false),
    (true, true, false), (true, true, true), ?_, ?_, ?_, ?_, ?_⟩
  · exact every_code_is_perfect _
  · exact every_code_is_perfect _
  · exact every_code_is_perfect _
  · exact every_code_is_perfect _
  · decide

-- A matching selects one outgoing arc per vertex in the inverse image F⁻¹(M).
-- For the four representatives above, the all-zero selection has two directed
-- cycles, while flipping the first component yields one Hamiltonian cycle.
def orbitFromZero (m : Vertex → Vertex) : Nat → Vertex
  | 0 => 0
  | n + 1 => m (orbitFromZero m n)

def oneCycle (m : Vertex → Vertex) : Prop :=
  ∀ v : Vertex, ∃ k : Fin 6, orbitFromZero m k.val = v

theorem rank_criterion_is_nontrivial_on_witness :
    ¬ oneCycle (matching (false, false, false)) ∧
    oneCycle (matching (true, false, false)) := by
  unfold oneCycle
  decide

end ZhuRefutation
