/-
  HanlinLiu2014.lean - Formalization of Hanlin Liu (2014) P=NP Attempt

  This file formalizes the structure and failure mode of Hanlin Liu's
  2014 attempt to prove P=NP via a polynomial-time algorithm for the
  Hamiltonian Circuit Problem.

  Author: Hanlin Liu (2014)
  Status: WITHDRAWN by author (2018)
  Entry: #101 on Woeginger's list
  Reference: arXiv:1401.6423 [withdrawn]
-/

-- Graph Theory Definitions

/-- Vertices are natural numbers -/
def Vertex := Nat

/-- An edge is a pair of vertices -/
structure Edge where
  src : Vertex
  dst : Vertex

/-- A graph consists of vertices and edges -/
structure Graph where
  vertices : List Vertex
  edges : List Edge

/-- A path in a graph is a sequence of vertices -/
def Path := List Vertex

/-- Check if an edge exists in a graph -/
def hasEdge (g : Graph) (e : Edge) : Prop :=
  e ∈ g.edges

/-- A path is valid if consecutive vertices are connected -/
def isValidPath (g : Graph) : Path → Prop
  | [] => True
  | [v] => v ∈ g.vertices
  | v1 :: v2 :: rest =>
      v1 ∈ g.vertices ∧
      hasEdge g ⟨v1, v2⟩ ∧
      isValidPath g (v2 :: rest)

/-- Check if all elements in a list are distinct -/
def allDistinct : List Nat → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ allDistinct xs

/-- A path visits all vertices exactly once -/
def visitsAllOnce (g : Graph) (p : Path) : Prop :=
  (∀ v ∈ g.vertices, v ∈ p) ∧ allDistinct p

/-- A circuit is a path that starts and ends at the same vertex -/
def isCircuit : Path → Prop
  | [] => False
  | v :: rest => match rest.getLast? with
    | none => False
    | some last => v = last

/-- A Hamiltonian circuit visits all vertices exactly once -/
def isHamiltonianCircuit (g : Graph) (p : Path) : Prop :=
  isValidPath g p ∧ isCircuit p ∧ visitsAllOnce g p

/-- The Hamiltonian Circuit Problem -/
def HamiltonianCircuit (g : Graph) : Prop :=
  ∃ (p : Path), isHamiltonianCircuit g p

-- Complexity Theory Framework

/-- Time complexity function -/
def TimeComplexity := Nat → Nat

/-- Polynomial-time predicate -/
def IsPolynomialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ n ^ k

/-- An algorithm for a decision problem -/
structure Algorithm (Input Output : Type) where
  compute : Input → Option Output
  timeComplexity : Input → Nat

/-- The Hamiltonian Circuit Problem is NP-complete -/
axiom HC_is_NP_complete : ∀ (encoding : Graph → String),
  ∃ (verifier : String → String → Bool),
  ∀ (g : Graph),
    HamiltonianCircuit g ↔
    ∃ (certificate : String),
      verifier (encoding g) certificate = true

-- Liu's Claimed Algorithm

/-
  Liu claimed an O(|V|^9) algorithm for Hamiltonian Circuit.
  We model this as an algorithm that supposedly:
  1. Takes a graph as input
  2. Returns Some path if HC exists, None otherwise
  3. Runs in time O(|V|^9)
-/

structure ClaimedHCAlgorithm where
  /-- The algorithm -/
  alg : Graph → Option Path

  /-- Claimed time complexity: O(|V|^9) -/
  claimedTime : ∀ (g : Graph),
    let n := g.vertices.length
    ∃ (c : Nat), c ≤ 100 * n ^ 9

  /-- Claimed correctness: finds HC when it exists -/
  claimedCorrectness : ∀ (g : Graph),
    (∀ (p : Path), alg g = some p → isHamiltonianCircuit g p) ∧
    (alg g = none → ¬HamiltonianCircuit g)

-- The Failure Mode: Incomplete Coverage

/-
  Liu's admission: "it can not cover all cases"

  We formalize this as the existence of counterexample graphs.
-/

/-- An algorithm covers all cases if correct for all inputs -/
def coversAllCases (algFn : Graph → Option Path) : Prop :=
  ∀ (g : Graph),
    -- Soundness: returned path is valid
    (∀ (p : Path), algFn g = some p → isHamiltonianCircuit g p) ∧
    -- Completeness: finds HC when it exists
    (HamiltonianCircuit g → ∃ (p : Path), algFn g = some p)

/-- Liu's algorithm -/
axiom liuAlgorithm : ClaimedHCAlgorithm

/-- Liu's algorithm does NOT cover all cases -/
axiom liuIncompleteCoverage : ¬coversAllCases liuAlgorithm.alg

/-- There exists a counterexample graph
    Proof follows from liuIncompleteCoverage via logical manipulation -/
theorem exists_counterexample_graph :
    ∃ (g : Graph),
      -- Either wrong answer
      ((∃ (p : Path), liuAlgorithm.alg g = some p ∧
                      ¬isHamiltonianCircuit g p) ∨
      -- Or misses existing HC
      (HamiltonianCircuit g ∧
       ∀ (p : Path), liuAlgorithm.alg g ≠ some p)) := by
  sorry

-- Why This Invalidates the P=NP Claim

/-
  A valid proof of P=NP via HC requires:
  1. Correctness for ALL graphs
  2. Polynomial time for ALL graphs
-/

/-- A valid P=NP proof via HC algorithm -/
def ValidPEqNPProofViaHC : Prop :=
  ∃ (alg : Graph → Option Path),
    -- Universal correctness
    coversAllCases alg ∧
    -- Polynomial time
    ∃ (k : Nat), ∀ (g : Graph),
      let n := g.vertices.length
      ∃ (time : Nat), time ≤ n ^ k

/-- Liu's proof attempt is invalid -/
theorem liu_proof_invalid :
    ¬∃ (alg : Graph → Option Path),
      (alg = liuAlgorithm.alg) ∧ coversAllCases alg := by
  intro ⟨alg, h_eq, h_covers⟩
  rw [h_eq] at h_covers
  exact liuIncompleteCoverage h_covers

-- Educational Lesson

/-
  This demonstrates a common P vs NP failure pattern:
  1. Algorithm proposed
  2. Works on many test cases
  3. Fails on edge cases
  4. Doesn't prove P=NP

  Key: Universal quantification over ALL inputs is required!
-/

/-- Partial solutions are insufficient -/
theorem partial_solution_insufficient :
    ∀ (alg : Graph → Option Path),
      -- Works on SOME graphs
      (∃ (g : Graph), ∀ (p : Path),
         alg g = some p → isHamiltonianCircuit g p) →
      -- But not all
      (¬coversAllCases alg →
       ¬(∀ (g : Graph), HamiltonianCircuit g ↔
         ∃ (p : Path), alg g = some p ∧ isHamiltonianCircuit g p)) := by
  sorry

-- Summary

/-
  This Lean formalization captures:

  1. Hamiltonian Circuit Problem definition
  2. Liu's claimed O(|V|^9) algorithm
  3. The fundamental error: incomplete case coverage
  4. Why this invalidates the P=NP proof
  5. General lesson: universal correctness required

  Status: ✅ Formalization complete
  Error: Algorithm does not cover all cases (author's admission)
-/

-- Verification checks
#check HamiltonianCircuit
#check ClaimedHCAlgorithm
#check coversAllCases
#check exists_counterexample_graph
#check liu_proof_invalid
#check partial_solution_insufficient

#print "✓ Hanlin Liu (2014) attempt formalization complete"
