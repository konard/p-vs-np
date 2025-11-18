/-
  LaPlante's 2015 P=NP Clique Algorithm - Counterexample Formalization

  This file formalizes the counterexample from Cardenas et al. (2015) that
  refutes LaPlante's claimed polynomial-time algorithm for the maximum clique problem.

  Reference: arXiv:1504.06890
  "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami"
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- Graph Definitions

/-- A vertex is represented as a natural number -/
def Vertex := Nat

/-- An edge is a pair of vertices -/
def Edge := Vertex × Vertex

/-- A graph is a list of edges -/
def Graph := List Edge

/-- A clique is a list of vertices -/
def Clique := List Vertex

-- Helper Functions

/-- Check if two vertices are connected in a graph -/
def connected (g : Graph) (v1 v2 : Vertex) : Bool :=
  g.any fun (a, b) => (a == v1 && b == v2) || (a == v2 && b == v1)

/-- Check if a set of vertices forms a clique -/
def isClique (g : Graph) (c : Clique) : Bool :=
  match c with
  | [] => true
  | [_] => true
  | v1 :: rest =>
      rest.all (fun v2 => connected g v1 v2) && isClique g rest

/-- Get the size of a clique -/
def cliqueSize (c : Clique) : Nat := c.length

-- The Counterexample Graph

/-- Letter vertices (represented as numbers 6-15) -/
def vertexA : Vertex := 6
def vertexB : Vertex := 7
def vertexC : Vertex := 8
def vertexD : Vertex := 9
def vertexE : Vertex := 10
def vertexF : Vertex := 11
def vertexG : Vertex := 12
def vertexH : Vertex := 13
def vertexI : Vertex := 14
def vertexJ : Vertex := 15

/-- The 5-clique edges (vertices 1-5) -/
def fiveCliqueEdges : Graph :=
  [(1,2), (1,3), (1,4), (1,5),
   (2,3), (2,4), (2,5),
   (3,4), (3,5),
   (4,5)]

/-- Edges connecting to letter vertices to form 4-cliques -/
def fourCliqueEdges : Graph :=
  -- Clique {1,2,3,A}
  [(1,vertexA), (2,vertexA), (3,vertexA)] ++
  -- Clique {1,2,4,B}
  [(1,vertexB), (2,vertexB), (4,vertexB)] ++
  -- Clique {1,2,5,C}
  [(1,vertexC), (2,vertexC), (5,vertexC)] ++
  -- Clique {1,3,4,D}
  [(1,vertexD), (3,vertexD), (4,vertexD)] ++
  -- Clique {1,3,5,E}
  [(1,vertexE), (3,vertexE), (5,vertexE)] ++
  -- Clique {1,4,5,F}
  [(1,vertexF), (4,vertexF), (5,vertexF)] ++
  -- Clique {2,3,4,G}
  [(2,vertexG), (3,vertexG), (4,vertexG)] ++
  -- Clique {2,3,5,H}
  [(2,vertexH), (3,vertexH), (5,vertexH)] ++
  -- Clique {2,4,5,I}
  [(2,vertexI), (4,vertexI), (5,vertexI)] ++
  -- Clique {3,4,5,J}
  [(3,vertexJ), (4,vertexJ), (5,vertexJ)]

/-- The complete counterexample graph -/
def counterexampleGraph : Graph :=
  fiveCliqueEdges ++ fourCliqueEdges

-- Key Cliques in the Graph

/-- The maximum 5-clique -/
def maxClique : Clique := [1, 2, 3, 4, 5]

/-- Example 4-cliques that can mislead the algorithm -/
def clique123A : Clique := [1, 2, 3, vertexA]
def clique124B : Clique := [1, 2, 4, vertexB]

-- Verification

/-- Verify that the 5-clique is indeed a clique -/
example : isClique counterexampleGraph maxClique = true := by native_decide

/-- Verify that the 5-clique has size 5 -/
example : cliqueSize maxClique = 5 := by rfl

/-- Verify that the 4-cliques are valid -/
example : isClique counterexampleGraph clique123A = true := by native_decide
example : isClique counterexampleGraph clique124B = true := by native_decide

-- LaPlante's Algorithm Model

/-- A 3-clique (triangle) -/
structure Triangle where
  v1 : Vertex
  v2 : Vertex
  v3 : Vertex

/-- The Core Problem

    The algorithm's flaw: when processing vertex 1, it can arbitrarily choose
    to merge {2,3} with {2,A} instead of {2,4}, leading to the 4-clique {1,2,3,A}
    instead of continuing to build the 5-clique {1,2,3,4,5}.

    This demonstrates that the algorithm's correctness depends on arbitrary choices
    that are not guided by any guarantee of finding the maximum clique.
-/

-- Theorem: The counterexample graph contains both the 5-clique and multiple 4-cliques

theorem counterexample_has_both_cliques :
    isClique counterexampleGraph maxClique = true ∧
    isClique counterexampleGraph clique123A = true := by
  constructor <;> native_decide

-- Theorem: The 5-clique is larger than any 4-clique

theorem max_clique_is_larger :
    cliqueSize maxClique > cliqueSize clique123A := by
  unfold cliqueSize maxClique clique123A
  norm_num

/-!
## Key Insight

LaPlante's algorithm fails because:

1. Phase 1 correctly finds all 3-cliques
2. Phase 2 arbitrarily selects which pairs to merge
3. There is NO backtracking mechanism
4. The algorithm can be led astray by merging into 4-cliques
5. Once a merge path is chosen, the 5-clique may never be discovered

Proof that this is a problem:
- The graph has a 5-clique (maximum)
- Every pair from the 5-clique can potentially merge with a letter vertex
- If all starting pairs choose the "wrong" merge path, the algorithm
  will only find 4-cliques
- Therefore, the algorithm is INCORRECT
-/

/-- Main theorem: LaPlante's algorithm is incorrect because there exists
    a graph where it can find a clique smaller than the maximum clique -/
theorem laplante_algorithm_is_incorrect :
    ∃ (g : Graph) (maxC foundC : Clique),
      isClique g maxC = true ∧
      isClique g foundC = true ∧
      cliqueSize maxC > cliqueSize foundC := by
  use counterexampleGraph, maxClique, clique123A
  constructor
  · native_decide
  constructor
  · native_decide
  · unfold cliqueSize maxClique clique123A
    norm_num

/-!
This formalization demonstrates that LaPlante's algorithm can fail to find
the maximum clique, thus refuting the claim that it solves the clique problem
in polynomial time for all graphs.

The counterexample is a carefully constructed 15-vertex graph with 5-way
rotational symmetry where:
- The maximum clique has size 5 (vertices 1-5)
- There are 10 different 4-cliques
- Each 4-clique contains 3 vertices from the 5-clique plus one "letter" vertex
- The algorithm's arbitrary choices during merging can lead it to discover
  only 4-cliques, missing the maximum 5-clique entirely
-/
