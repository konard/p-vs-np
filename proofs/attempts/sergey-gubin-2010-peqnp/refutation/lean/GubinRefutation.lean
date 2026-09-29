/-!
  A sound audit of the abstract LP claims previously attributed to Gubin.

  The paper's actual variables, inequalities, projection and vertex action have
  not been encoded here. The examples below are small LPs, not Gubin's
  formulation, and no theorem here claims to refute that formulation.
-/

namespace GubinAudit

abbrev Coordinates (n : Nat) := Fin n → Rat

/-- An LP feasible region. Concrete examples below supply linear equalities. -/
structure LPProblem where
  numVars : Nat
  feasible : Coordinates numVars → Prop

/-- A feasible point that is not a strict convex combination of distinct
    feasible points. -/
def IsVertex (lp : LPProblem) (x : Coordinates lp.numVars) : Prop :=
  lp.feasible x ∧
    ∀ y z : Coordinates lp.numVars, ∀ t : Rat,
      0 < t → t < 1 → lp.feasible y → lp.feasible z →
      x = (fun i => t * y i + (1 - t) * z i) → y = x ∧ z = x

structure ExtremePoint (lp : LPProblem) where
  x : Coordinates lp.numVars
  isVertex : IsVertex lp x

def IsIntegral (lp : LPProblem) (x : Coordinates lp.numVars) : Prop :=
  ∀ i : Fin lp.numVars, ∃ z : Int, x i = (z : Rat)

/-- A directed graph includes its edge relation, rather than only weights. -/
structure DirectedGraph where
  numNodes : Nat
  edge : Fin numNodes → Fin numNodes → Prop

/-- A tour is a permutation whose consecutive vertices, including the last
    and first, are joined by directed edges. -/
structure ATSPTour (g : DirectedGraph) where
  order : Fin g.numNodes → Fin g.numNodes
  injective : ∀ i j, order i = order j → i = j
  surjective : ∀ j, ∃ i, order i = j
  cycleEdges : ∀ i j : Fin g.numNodes,
    j.val = (i.val + 1) % g.numNodes → g.edge (order i) (order j)

/-- The claimed correspondence needs an actual encoding of each tour as an LP
    point. Merely producing some integral vertex loses that information. -/
def HasIntegralCorrespondence (g : DirectedGraph) (lp : LPProblem)
    (encode : ATSPTour g → Coordinates lp.numVars) : Prop :=
  (∀ tour, ∃ ep : ExtremePoint lp,
    ep.x = encode tour ∧ IsIntegral lp ep.x) ∧
  (∀ ep : ExtremePoint lp, IsIntegral lp ep.x →
    ∃ tour, encode tour = ep.x)

/-- Coordinate symmetry is invariance of feasibility under every variable
    permutation. The paper's vertex-relabeling symmetry would additionally
    require an action on its particular extended variables. -/
def IsCoordinateSymmetric (lp : LPProblem) : Prop :=
  ∀ σ : Fin lp.numVars → Fin lp.numVars,
    (∀ i j, σ i = σ j → i = j) → (∀ j, ∃ i, σ i = j) →
    ∀ x, lp.feasible x ↔ lp.feasible (x ∘ σ)

private def halfPoint : Coordinates 2 :=
  fun i => if i = 0 then (1 / 2 : Rat) else 0

/-- The two linear equations x₀ = 1/2 and x₁ = 0 define a singleton LP. -/
private def halfLP : LPProblem :=
  ⟨2, fun x => x 0 = (1 / 2 : Rat) ∧ x 1 = 0⟩

private theorem half_feasible : halfLP.feasible halfPoint := by
  constructor <;> rfl

private theorem half_unique (x : Coordinates 2)
    (hx : halfLP.feasible x) : x = halfPoint := by
  apply funext
  intro i
  have h : ∀ i : Fin 2, x i = halfPoint i :=
    (Fin.forall_fin_two).2 ⟨hx.1, hx.2⟩
  exact h i

private theorem half_vertex : IsVertex halfLP halfPoint := by
  constructor
  · exact half_feasible
  · intro y z t _ _ hy hz _
    exact ⟨half_unique y hy, half_unique z hz⟩

private theorem half_not_integral : ¬IsIntegral halfLP halfPoint := by
  intro h
  change (∀ i : Fin 2, ∃ z : Int, halfPoint i = (z : Rat)) at h
  obtain ⟨z, hz⟩ := h 0
  have hden := congrArg Rat.den hz
  have htwo : (halfPoint 0).den = 2 := by decide +kernel
  have hone : ((z : Rat)).den = 1 := Rat.den_intCast z
  rw [htwo, hone] at hden
  contradiction

/-- A concrete fractional extreme point, derived from linear equations. -/
theorem fractional_vertex_exists :
    ∃ lp : LPProblem, ∃ ep : ExtremePoint lp, ¬IsIntegral lp ep.x := by
  exact ⟨halfLP, ⟨halfPoint, half_vertex⟩, half_not_integral⟩

private def swap : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

private theorem half_asymmetric : ¬IsCoordinateSymmetric halfLP := by
  intro hs
  have hinj : ∀ i j : Fin 2, swap i = swap j → i = j := by decide
  have hsurj : ∀ j : Fin 2, ∃ i, swap i = j := by decide
  have h := (hs swap hinj hsurj halfPoint).1 half_feasible
  have hzero : (halfPoint ∘ swap) 0 = (1 / 2 : Rat) := h.1
  have hne : (0 : Rat) ≠ 1 / 2 := by decide +kernel
  exact hne hzero

/-- A nonsymmetric LP can have a fractional vertex. This refutes the general
    implication from coordinate asymmetry to integrality. -/
theorem asymmetry_does_not_imply_integrality :
    ∃ lp : LPProblem, ¬IsCoordinateSymmetric lp ∧
      ∃ ep : ExtremePoint lp, ¬IsIntegral lp ep.x := by
  exact ⟨halfLP, half_asymmetric, ⟨halfPoint, half_vertex⟩, half_not_integral⟩

/-- A one-vertex graph with no self-loop has no tour. -/
private def noEdgeGraph : DirectedGraph := ⟨1, fun _ _ => False⟩

private theorem no_tour : ATSPTour noEdgeGraph → False := by
  intro tour
  exact tour.cycleEdges ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)

/-- The equation x₀ = 0 gives an integral extreme point. -/
private def zeroLP : LPProblem := ⟨1, fun x => x 0 = 0⟩
private def zeroPoint : Coordinates 1 := fun _ => 0

private theorem zero_unique (x : Coordinates 1)
    (hx : zeroLP.feasible x) : x = zeroPoint := by
  apply funext
  intro i
  have h : ∀ i : Fin 1, x i = zeroPoint i :=
    (Fin.forall_fin_one).2 hx
  exact h i

private theorem zero_vertex : IsVertex zeroLP zeroPoint := by
  constructor
  · rfl
  · intro y z t _ _ hy hz _
    exact ⟨zero_unique y hy, zero_unique z hz⟩

private theorem zero_integral : IsIntegral zeroLP zeroPoint := by
  intro i
  exact ⟨0, rfl⟩

/-- Size and integrality alone do not establish a tour correspondence.
    This is an illustrative LP, not the LP from Gubin's paper. -/
theorem abstract_correspondence_can_fail
    (encode : ATSPTour noEdgeGraph → Coordinates zeroLP.numVars) :
    ¬HasIntegralCorrespondence noEdgeGraph zeroLP encode := by
  intro h
  obtain ⟨tour, _⟩ := h.2 ⟨zeroPoint, zero_vertex⟩ zero_integral
  exact no_tour tour

end GubinAudit
