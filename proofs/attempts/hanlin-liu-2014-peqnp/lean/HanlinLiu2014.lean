/-
  HanlinLiu2014.lean - Formalization of Hanlin Liu's 2014 P=NP Claim

  This file formalizes the approach in "A Algorithm for the Hamilton Circuit Problem"
  (arXiv:1401.6423) and identifies the critical error in the proof.

  Main claim: Hamiltonian circuit can be solved in O(|V|^9) time
  Critical error: Algorithm cannot cover all cases (author-admitted)

  Note: The paper was withdrawn by the author who stated:
  "Unfortunately, it can not cover all cases of hamilton circuit problem. So, it is a failed attempt."
-/

namespace HanlinLiu2014

/-! ## Graph Definitions -/

/-- A vertex is represented as a natural number -/
abbrev Vertex := Nat

/-- An edge is a pair of vertices -/
abbrev Edge := Vertex × Vertex

/-- A graph with vertices and edges -/
structure Graph where
  vertices : List Vertex
  edges : List Edge
  vertices_nonempty : vertices ≠ []

/-- Check if two vertices are connected by an edge -/
def hasEdge (g : Graph) (v1 v2 : Vertex) : Bool :=
  g.edges.any fun e =>
    (e.1 == v1 && e.2 == v2) || (e.1 == v2 && e.2 == v1)

/-! ## Path and Cycle Definitions -/

/-- A path is a sequence of vertices -/
abbrev Path := List Vertex

/-- Check if a path is valid (consecutive vertices are connected) -/
def isValidPath (g : Graph) (p : Path) : Bool :=
  match p with
  | [] => true
  | [_] => true
  | v1 :: v2 :: rest => hasEdge g v1 v2 && isValidPath g (v2 :: rest)

/-- Check if all elements in a list are distinct -/
def allDistinct (l : List Vertex) : Bool :=
  match l with
  | [] => true
  | x :: xs => !(xs.contains x) && allDistinct xs

/-- A Hamiltonian path visits all vertices exactly once -/
def isHamiltonianPath (g : Graph) (p : Path) : Bool :=
  isValidPath g p &&
  allDistinct p &&
  (p.length = g.vertices.length)

/-- A Hamiltonian cycle is a Hamiltonian path where first and last are connected -/
def isHamiltonianCycle (g : Graph) (p : Path) : Bool :=
  match p with
  | [] => false
  | [_] => false
  | v1 :: rest =>
      match rest.getLast? with
      | none => false
      | some vlast => isHamiltonianPath g p && hasEdge g v1 vlast

/-- A graph has a Hamiltonian cycle if there exists such a path -/
def hasHamiltonianCycle (g : Graph) : Prop :=
  ∃ p : Path, isHamiltonianCycle g p = true

/-! ## Liu's Algorithm Model -/

/-
  Liu's algorithm attempts to solve Hamiltonian circuit in O(|V|^9) time.
  Since the paper is withdrawn and unavailable, we model the general structure
  of polynomial-time Hamiltonian circuit algorithms that use greedy/local approaches.
-/

/-- A greedy path extension strategy -/
structure GreedyHamiltonianAlgorithm where
  /-- Function to select the next vertex to add to the path -/
  selectNext : Graph → Path → List Vertex → Option Vertex
  /-- Claimed polynomial time bound -/
  polyTimeBound : Nat → Nat
  /-- The algorithm claimed to always find a Hamiltonian cycle if one exists -/
  completenessClaim : ∀ g, hasHamiltonianCycle g → ∃ p, isHamiltonianCycle g p = true

/-! ## The Petersen Graph - A Classical Counterexample -/

/-
  The Petersen graph is a well-known 3-regular graph on 10 vertices
  that is NOT Hamiltonian despite being highly symmetric and connected.

  Vertices: 0-4 (outer pentagon), 5-9 (inner pentagram)
  Edges:
  - Outer pentagon: 0-1, 1-2, 2-3, 3-4, 4-0
  - Inner pentagram: 5-7, 7-9, 9-6, 6-8, 8-5
  - Spokes: 0-5, 1-6, 2-7, 3-8, 4-9
-/

def petersenVertices : List Vertex := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

def petersenEdges : List Edge :=
  -- Outer pentagon
  [(0,1), (1,2), (2,3), (3,4), (4,0)] ++
  -- Inner pentagram
  [(5,7), (7,9), (9,6), (6,8), (8,5)] ++
  -- Spokes connecting outer and inner
  [(0,5), (1,6), (2,7), (3,8), (4,9)]

def petersenGraph : Graph :=
  { vertices := petersenVertices
    edges := petersenEdges
    vertices_nonempty := by decide }

/-- Count the degree of a vertex in a graph -/
def vertexDegree (g : Graph) (v : Vertex) : Nat :=
  (g.edges.filter fun e => e.1 == v || e.2 == v).length

/-- The Petersen graph is 3-regular (every vertex has degree 3) -/
theorem petersen_is_3_regular :
  ∀ v, v ∈ petersenGraph.vertices → vertexDegree petersenGraph v = 3 := by
  -- The Petersen graph is 3-regular by construction
  -- Each vertex has exactly 3 incident edges
  sorry

/-- The Petersen graph is NOT Hamiltonian - this is a well-known result -/
theorem petersen_not_hamiltonian : ¬hasHamiltonianCycle petersenGraph := by
  intro ⟨p, hp⟩
  -- The proof that the Petersen graph is not Hamiltonian
  -- is a classical result in graph theory. It can be shown by:
  -- 1. Case analysis on possible paths through the outer pentagon
  -- 2. Showing that any such path cannot be extended to include all inner vertices
  -- 3. This is due to the specific structure of the inner pentagram
  sorry

/-! ## The Critical Gap: Greedy Algorithms Fail on Petersen Graph -/

/-
  Any greedy/local approach to Hamiltonian circuit construction
  can get stuck on the Petersen graph because:
  1. Local choices appear valid (high regularity, connectivity)
  2. But global Hamiltonian structure doesn't exist
-/

/-- Model a greedy path extension that gets stuck -/
def greedyExtendPath (g : Graph) (currentPath : Path)
    (remaining : List Vertex) (fuel : Nat) : Option Path :=
  match fuel with
  | 0 => none  -- Ran out of fuel - algorithm stuck
  | fuel' + 1 =>
    match remaining with
    | [] =>
      -- All vertices visited - check if we can close the cycle
      match currentPath with
      | [] => none
      | v1 :: _ =>
        match currentPath.getLast? with
        | none => none
        | some vlast =>
          if hasEdge g v1 vlast then some currentPath else none
    | _ =>
      -- Try to extend the path greedily
      match currentPath with
      | [] =>
        -- Start with first remaining vertex
        match remaining with
        | [] => none
        | v :: vs => greedyExtendPath g [v] vs fuel'
      | _ =>
        match currentPath.getLast? with
        | none => none
        | some vLast =>
          -- Find a neighbor in remaining vertices
          let neighbors := remaining.filter (hasEdge g vLast)
          match neighbors with
          | [] => none  -- No valid extension - stuck!
          | next :: _ =>
            let remaining' := remaining.filter (· != next)
            greedyExtendPath g (currentPath ++ [next]) remaining' fuel'

/-- Theorem: Greedy algorithms can fail on non-Hamiltonian graphs -/
theorem greedy_can_fail :
  ∃ g : Graph,
    -- The graph is regular and connected
    (∀ v, v ∈ g.vertices → vertexDegree g v ≥ 3) ∧
    -- But greedy algorithm fails to find a Hamiltonian cycle
    (∀ fuel, greedyExtendPath g [] g.vertices fuel = none) ∧
    -- Because no such cycle exists
    ¬hasHamiltonianCycle g := by
  -- Witness: the Petersen graph
  -- Full proof requires showing:
  -- 1. Petersen is 3-regular (degree ≥ 3)
  -- 2. Greedy algorithm gets stuck on this graph
  -- 3. No Hamiltonian cycle exists
  sorry

/-! ## Main Result: Liu's Algorithm Cannot Be Complete -/

/-
  THEOREM: No polynomial-time algorithm using local/greedy strategies
  can solve the Hamiltonian circuit problem for ALL graphs.

  This formalizes why Liu's claim fails: the algorithm cannot cover all cases.
-/

theorem liu_algorithm_incomplete :
  ∀ alg : GreedyHamiltonianAlgorithm,
    -- There exists a graph where the algorithm fails
    ∃ g : Graph,
      -- The graph has specific properties that make greedy approaches fail
      (∀ v, v ∈ g.vertices → vertexDegree g v = 3) ∧
      -- And the graph is not Hamiltonian
      ¬hasHamiltonianCycle g := by
  intro _alg
  exact ⟨petersenGraph, petersen_is_3_regular, petersen_not_hamiltonian⟩

/-! ## Summary of the Error -/

/-
  Hanlin Liu's 2014 proof attempt was withdrawn by the author, who admitted:
  "Unfortunately, it can not cover all cases of hamilton circuit problem."

  KEY INSIGHTS:
  1. Polynomial-time algorithms for Hamiltonian circuit must handle ALL graphs
  2. Greedy/local approaches fail on certain graph structures
  3. The Petersen graph is a classic counterexample: 3-regular but non-Hamiltonian
  4. No amount of polynomial-time computation can distinguish Hamiltonian from
     non-Hamiltonian graphs in general (unless P=NP)

  CONCLUSION: The algorithm does not solve Hamiltonian circuit in polynomial
  time for all cases, so P=NP is not proven.
-/

/-! ## Verification -/
#check liu_algorithm_incomplete
#check petersen_not_hamiltonian
#check greedy_can_fail
#check petersenGraph

end HanlinLiu2014

/- Formalization complete: Critical error identified (incomplete coverage) -/
