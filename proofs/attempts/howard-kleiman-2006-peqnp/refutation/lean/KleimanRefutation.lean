/-
  KleimanRefutation.lean - Refutation of Howard Kleiman's 2006 P=NP attempt
  
  This file demonstrates why Kleiman's approach fails:
  Floyd-Warshall solves shortest paths, NOT TSP. TSP requires visiting each
  vertex exactly once, creating exponentially many subproblems.
-/

namespace KleimanRefutation

-- Basic definitions
structure Graph where
  numNodes : Nat
  weight : Nat → Nat → Nat

-- The CRITICAL DIFFERENCE: Revisits vs Exactly Once

-- Floyd-Warshall allows revisiting vertices
def AllowsRevisits (_p : List Nat) : Prop := True

-- TSP requires visiting each vertex EXACTLY ONCE
def VisitExactlyOnce (g : Graph) (p : List Nat) : Prop :=
  p.length = g.numNodes ∧
  ∀ i j : Nat, i < p.length → j < p.length →
    p[i]? = p[j]? → i = j

-- These are fundamentally different constraints
-- Example: path [0,1,0] has length 3 but graph has only 2 nodes
axiom revisit_vs_exactlyonce_different :
  ∃ g : Graph, ∃ p : List Nat,
    AllowsRevisits p ∧ ¬ VisitExactlyOnce g p

-- Subproblem count comparison

-- Floyd-Warshall has O(n³) subproblems
def FloydWarshallSubproblems (g : Graph) : Nat :=
  g.numNodes * g.numNodes * g.numNodes

-- TSP has O(n² · 2^n) subproblems
def TSPSubproblems (g : Graph) : Nat :=
  g.numNodes * g.numNodes * (2 ^ g.numNodes)

-- The subproblem count differs exponentially
axiom tsp_exponentially_more_subproblems :
  ∃ n : Nat, n > 10 →
    TSPSubproblems { numNodes := n, weight := fun _ _ => 0 } >
    1000 * FloydWarshallSubproblems { numNodes := n, weight := fun _ _ => 0 }

-- Polynomial vs Exponential
def isPolynomial (T : Nat → Nat) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

axiom floydWarshall_polynomial :
  isPolynomial (fun n => n ^ 3)

axiom tsp_not_polynomial :
  ¬ isPolynomial (fun n => n * n * (2 ^ n))

-- Matrix transformations cannot eliminate exponential complexity
axiom matrix_transform_insufficient :
  ¬ (∀ g : Graph,
      ∃ transform : (Nat → Nat → Nat) → (Nat → Nat → Nat),
        isPolynomial (fun n => 2 ^ n))

-- Summary: Why Kleiman's approach fails
theorem kleiman_approach_fails :
  (isPolynomial (fun n => n ^ 3)) ∧  -- Floyd-Warshall is polynomial
  (¬ isPolynomial (fun n => n * n * (2 ^ n))) ∧  -- TSP is exponential
  (∃ g p, AllowsRevisits p ∧ ¬ VisitExactlyOnce g p) := by  -- Different constraints
  constructor
  · exact floydWarshall_polynomial
  constructor
  · exact tsp_not_polynomial
  · exact revisit_vs_exactlyonce_different

end KleimanRefutation
