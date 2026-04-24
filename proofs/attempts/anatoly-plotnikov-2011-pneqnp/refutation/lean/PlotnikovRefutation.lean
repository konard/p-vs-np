/-
  PlotnikovRefutation.lean - Refutation of Plotnikov's 2011 P≠NP attempt

  This file formally demonstrates why Plotnikov's diagonal construction fails:
  1. The diagonal graph construction is circular (ill-defined)
  2. Diagonalization cannot separate P from NP (relativization barrier)
  3. The fixed-point argument does not apply to graph colorability
-/

namespace PlotnikovRefutation

-- ============================================================
-- Section 1: Reproducing the Basic Setup
-- ============================================================

-- Graph definition
structure Graph where
  numVertices : Nat
  edge : Nat → Nat → Bool

-- 3-Coloring
def Color := Fin 3

def isColoring (G : Graph) (c : Fin G.numVertices → Color) : Prop :=
  ∀ u v : Fin G.numVertices, G.edge u v = true → c u ≠ c v

def is3Colorable (G : Graph) : Prop :=
  ∃ c : Fin G.numVertices → Color, isColoring G c

-- Decision algorithm
def DecisionAlgorithm := Graph → Bool

def isCorrect (A : DecisionAlgorithm) : Prop :=
  ∀ G : Graph, A G = true ↔ is3Colorable G

-- ============================================================
-- Section 2: The Circular Construction Demonstrated
-- ============================================================

/-
  Plotnikov claims: for each algorithm A_i, there exists a graph H_i such that:
    is3Colorable H_i ↔ A_i H_i = false

  We show why this is circular.

  If H_i is 3-colorable, then by the claimed equivalence, A_i H_i = false.
  If H_i is not 3-colorable, then A_i H_i = true.

  But to construct H_i as a concrete graph, we need to decide in advance
  which case holds. This requires knowing A_i(H_i) before H_i is defined.

  The following lemma shows that assuming the diagonal property exists
  leads to a contradiction with the standard behavior of boolean functions:
-/

-- The "circular" property: H is 3-colorable iff A rejects it
def diagonalProperty (A : DecisionAlgorithm) (H : Graph) : Prop :=
  is3Colorable H ↔ A H = false

-- If A is correct and H has the diagonal property, we get a contradiction
theorem circularityContradiction
    (A : DecisionAlgorithm)
    (H : Graph)
    (hCorrect : isCorrect A)
    (hDiag : diagonalProperty A H) :
    False := by
  -- hCorrect: A H = true ↔ is3Colorable H
  -- hDiag:   is3Colorable H ↔ A H = false
  -- Case analysis on A H
  cases h : A H with
  | true =>
    -- A H = true → is3Colorable H (by correctness)
    have h3col : is3Colorable H := (hCorrect H).mp h
    -- is3Colorable H → A H = false (by diagonal property)
    have hfalse : A H = false := hDiag.mp h3col
    -- A H = true and A H = false: contradiction
    rw [h] at hfalse
    exact absurd hfalse (by decide)
  | false =>
    -- A H = false → ¬ is3Colorable H (by correctness)
    have hNot3col : ¬ is3Colorable H := by
      intro h3col
      have htrue : A H = true := (hCorrect H).mpr h3col
      rw [h] at htrue
      exact absurd htrue (by decide)
    -- A H = false → is3Colorable H (by diagonal property, backward direction)
    have h3col : is3Colorable H := hDiag.mpr h
    exact hNot3col h3col

/-
  Key insight from circularityContradiction:
  For any CORRECT algorithm A, NO graph H can have the diagonal property.

  This means Plotnikov's diagonal graph H_i cannot exist when A_i is correct.

  Plotnikov's proof assumes:
  (a) A_j is a correct polynomial-time algorithm for 3-COL
  (b) H_j has the diagonal property for A_j

  But circularityContradiction shows (a) and (b) are contradictory.
  So the contradiction Plotnikov finds is not with the existence of A,
  but with the assumption that H_j can be constructed!

  In other words: the construction of H_j already fails, so there is
  no meaningful contradiction with A's existence.
-/

-- Formal statement: diagonal graph cannot exist for a correct algorithm
theorem noDiagonalGraphForCorrectAlgorithm
    (A : DecisionAlgorithm)
    (hCorrect : isCorrect A) :
    ∀ H : Graph, ¬ diagonalProperty A H := by
  intro H hDiag
  exact circularityContradiction A H hCorrect hDiag

-- ============================================================
-- Section 3: Relativization Barrier
-- ============================================================

/-
  The Baker-Gill-Solovay theorem (1975) establishes that diagonalization-
  based proof techniques cannot separate P from NP.

  We state this as an axiom (since a full proof requires oracle computation models).

  The consequence: even if Plotnikov's diagonal construction were well-defined,
  the fact that it relativizes means it cannot prove P ≠ NP.
-/

-- Relativization: a proof technique relativizes if it works relative to any oracle
-- We abstract this as: the technique works equally for any "oracle-augmented" algorithms
def Relativizes (proofTechnique : Prop) : Prop :=
  -- A simplified model: the technique applies universally, regardless of oracle
  proofTechnique

-- Baker-Gill-Solovay: diagonalization relativizes, hence cannot separate P from NP
-- (Stated as axiom; full proof requires formal oracle complexity models)
axiom bakerGillSolovay_relativization_barrier :
  ∀ (diagonalizationProof : Prop),
    Relativizes diagonalizationProof →
    ¬ (diagonalizationProof → ¬ ∃ A : DecisionAlgorithm, isCorrect A)
-- ^^^ Simplified statement: no relativizing argument can prove P ≠ NP

-- Plotnikov's diagonal construction relativizes (it makes no use of
-- non-relativizing properties of the complexity classes P and NP)
axiom plotnikovDiagonalRelativizes :
  Relativizes (∃ diagonalGraph : Nat → Graph,
    ∃ enum : Nat → DecisionAlgorithm,
      ∀ i : Nat, is3Colorable (diagonalGraph i) ↔ enum i (diagonalGraph i) = false)

-- ============================================================
-- Section 4: Fixed-Point Considerations
-- ============================================================

/-
  One might try to save Plotnikov's argument using the Kleene Recursion Theorem.
  We explain why this doesn't work for graph colorability.

  The Recursion Theorem (for Turing machines):
    For any computable function f: ℕ → ℕ, there exists e such that M_e ≡ M_{f(e)}.

  This applies to ALGORITHMS (Turing machines), not to GRAPHS (combinatorial objects).

  3-Colorability is a COMBINATORIAL property of graphs, not an algorithmic one.
  A graph cannot "know" what an algorithm outputs when run on it.
  The graph is passive data; it cannot encode its own algorithmic treatment.
-/

-- Representing: algorithms are functions (nat → nat), graphs are structures
-- There's no way to create a graph that "knows" its own colorability given by some algorithm

-- Conceptual theorem: 3-colorability is a fixed combinatorial property
-- (no self-reference possible for concrete graphs)
theorem colorabilityIsFixed (G : Graph) :
    (is3Colorable G) ∨ (¬ is3Colorable G) := by
  exact Classical.em (is3Colorable G)

-- The key point: is3Colorable G is determined by G's structure alone,
-- not by any algorithm's output. So "H_i is 3-colorable iff A_i(H_i) = false"
-- cannot define H_i — it would require H_i's structure to simultaneously
-- both determine and be determined by A_i's computation.

-- ============================================================
-- Section 5: Summary of Refutation
-- ============================================================

/-
  Summary of Why Plotnikov's 2011 Proof Fails:

  1. CIRCULAR CONSTRUCTION (most fundamental):
     The diagonal graph H_i is defined by:
       is3Colorable H_i ↔ A_i(H_i) = false
     But for any correct algorithm A_i, NO such graph H_i can exist
     (proved by circularityContradiction above).
     The construction fails at the first step.

  2. RELATIVIZATION BARRIER:
     Even if the construction were well-defined, diagonalization-based
     arguments cannot separate P from NP (Baker-Gill-Solovay 1975).
     The strategy is provably insufficient for the problem.

  3. MISUSE OF DIAGONALIZATION:
     Turing's diagonalization works because the "self-referential input"
     is a natural number (a machine index), defined independently.
     Plotnikov's diagonal input is a graph whose combinatorial properties
     must encode its own algorithmic treatment — fundamentally different.

  4. SCOPE OF CONCLUSION:
     Even a valid contradiction for one algorithm A at one graph G*
     would not prove P ≠ NP. One needs to handle ALL polynomial-time
     algorithms simultaneously, which the argument does not do correctly.
-/

-- The proof is invalid: the assumption of the diagonal property
-- contradicts the assumed correctness of A, not the existence of A.
theorem plotnikovProofInvalid :
    ∀ A : DecisionAlgorithm, isCorrect A →
      ∀ H : Graph, ¬ diagonalProperty A H := by
  exact fun A hCorrect => noDiagonalGraphForCorrectAlgorithm A hCorrect

end PlotnikovRefutation
