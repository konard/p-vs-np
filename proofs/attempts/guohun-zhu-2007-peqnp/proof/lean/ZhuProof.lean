/-
  ZhuProof.lean - Forward formalization of Guohun Zhu's 2007 P=NP attempt

  This file formalizes the STRUCTURE of Zhu's argument (not a valid proof).
  The formalization shows what Zhu claimed, following the original paper
  "The Complexity of HCP in Digraphs with Degree Bound Two"
  (arXiv:0704.0309v3, July 2007).

  Status: This is a CLAIMED proof structure with fundamental errors.
          See refutation/ for why this fails.

  Note: We use Nat for vertex indices to avoid universe polymorphism issues.
        The formalization captures the logical structure without using Type*.
-/

namespace ZhuProof

-- Section 2: Definitions and Properties
--
-- "Throughout this paper we consider the finite simple (un)directed graph
--  D = (V, A), i.e. the graph has no multi-arcs and no self loops."

-- A directed graph D = (V, A) with n vertices (indexed 0..n-1)
structure Digraph where
  numVertices : Nat
  arcs : Nat → Nat → Bool

-- Out-degree of a vertex
-- "Let the out degree of vertex vi denoted by d+(vi)"
def outDegree (D : Digraph) (v : Nat) : Nat :=
  (List.range D.numVertices).filter (fun u => D.arcs v u) |>.length

-- In-degree of a vertex
-- "which has the in degree by denoted as d-(vi)"
def inDegree (D : Digraph) (v : Nat) : Nat :=
  (List.range D.numVertices).filter (fun u => D.arcs u v) |>.length

-- "Let us named a simple strong connected digraphs with at most indegree 1 or 2
--  and outdegree 2 or 1 as Γ digraphs."
structure GammaDigraph extends Digraph where
  strongly_connected : True  -- Simplified: strong connectivity
  in_degree_bound : True     -- Simplified: ∀ v, 1 ≤ d⁻(v) ≤ 2
  out_degree_bound : True    -- Simplified: ∀ v, 1 ≤ d⁺(v) ≤ 2

-- Lemma 1: Sufficient condition for Hamiltonian cycle
--
-- "If a digraph D(V,A) include a sub graph D'(V,L) with following two properties,
--  the D is a Hamiltonian graph:
--  c1. ∀vi ∈ D' → d+(vi) = 1 ∧ d−(vi) = 1,
--  c2. |L| = |V| ≥ 2 and D' is a strong connected digraph."

-- A Hamiltonian cycle: a subgraph where every vertex has in-degree 1 and out-degree 1,
-- and the subgraph is strongly connected
structure HamiltonianCycle (D : Digraph) where
  subgraph : Digraph
  is_subgraph : ∀ u v : Nat, subgraph.arcs u v = true → D.arcs u v = true
  degree_one : True   -- Simplified: ∀ v, d+(v) = d−(v) = 1 in subgraph
  is_connected : True  -- Simplified: subgraph is strongly connected
  covers_all : True    -- Simplified: |L| = |V|

-- Section 3: Projector Graph Construction
--
-- "Firstly, let us divided the matrix of C into two groups:
--  C+ = {cij | cij ≥ 0, otherwise 0}
--  C− = {cij | cij ≤ 0, otherwise 0}
--  Secondly, let us combined the C+ and C− as following matrix:
--  F = [C+; −C−]"

-- Balanced bipartite graph G(X,Y;E) with n vertices on each side
structure BipartiteGraph where
  numLeft : Nat   -- |X|
  numRight : Nat  -- |Y|
  edges : Nat → Nat → Bool

-- "The projector graph construction (Theorem 1):
--  Given an incidence matrix Cnm of Γ digraph, building a mapping:
--  F = [C+; −C−], then F is an incidence matrix of undirected balanced
--  bipartite graph G(X,Y;E)"
def projectorGraph (D : GammaDigraph) : BipartiteGraph :=
  { numLeft  := D.numVertices
    numRight := D.numVertices
    edges    := fun x y => D.arcs x y }  -- Placeholder for actual construction

-- Theorem 1: Properties of the projector graph
--
-- "c1. |X| = n, |Y| = n, |E| = m
--  c2. ∀xi ∈ X ∧ 1 ≤ d(xi) ≤ 2, ∀yi ∈ Y ∧ 1 ≤ d(yi) ≤ 2
--  c3. G has at most n/4 components which is length of 4."

-- CLAIM (Theorem 1): The projector graph has the stated properties
axiom theorem1_balanced : ∀ (D : GammaDigraph),
  True  -- |X| = |Y| = n

axiom theorem1_degree_bound : ∀ (D : GammaDigraph),
  True  -- ∀ x ∈ X, 1 ≤ d(x) ≤ 2; ∀ y ∈ Y, 1 ≤ d(y) ≤ 2

axiom theorem1_components : ∀ (D : GammaDigraph),
  True  -- G has at most n/4 components of length 4

-- Theorem 2: Hamiltonian Cycle ↔ Perfect Matching with rank condition
--
-- "Determining a Hamiltonian cycle in Γ digraph is equivalent to find
--  a perfect match M in G and r(C') = n − 1, where C' is the incidence
--  matrix of D'(V,L) ⊆ D and L = {ai | ai ∈ D ∧ ei ∈ M}."

-- A perfect matching in a bipartite graph
structure PerfectMatching (G : BipartiteGraph) where
  matching : Nat → Nat
  is_injective : True      -- Simplified: matching is injective
  edges_valid : ∀ x, x < G.numLeft → G.edges x (matching x) = true

-- The rank condition: r(C') = n - 1
def satisfiesRankCondition (n : Nat) : Prop := True  -- Simplified

-- CLAIM (Theorem 2): Hamiltonian cycle ↔ perfect matching with rank condition
axiom theorem2_forward : ∀ (D : GammaDigraph),
  HamiltonianCycle D.toDigraph →
  ∃ (G : BipartiteGraph) (M : PerfectMatching G),
    satisfiesRankCondition D.numVertices

axiom theorem2_backward : ∀ (D : GammaDigraph),
  (∃ (G : BipartiteGraph) (M : PerfectMatching G),
    satisfiesRankCondition D.numVertices) →
  HamiltonianCycle D.toDigraph

-- Section 5: Number of perfect matchings in projector graph
--
-- "Given a perfect matching M, each component(cycle) in G has two partition
--  edges belong to M. Let us code component Gi which |Gi| > 2 and matching M
--  to a binary variable."

-- Binary coding of a matching relative to components (Equation 9)
-- "code(M) = {0, 0, 1} or {0, 1, 0} etc."
def MatchingCode := List Bool

-- Lemma 4 (THE CRITICAL ERROR)
--
-- "The maximal number of labeled perfect matching in a projector graph G
--  is 2^(n/4), but the maximal number of unlabeled perfect matching in a
--  projector graph G is n/2."
--
-- NOTE: This is the FATAL error. The paper claims:
--   - k components with 2 choices each → 2k matchings (WRONG)
--   - Reality: k components with 2 choices each → 2^k matchings
--
-- The "isomorphism" argument does not reduce the exponential count because
-- different matchings (even if "isomorphic" as abstract graphs) correspond
-- to different arc selections in the original digraph D.

-- The paper's INCORRECT claim
-- WARNING: This axiom is FALSE. It is stated here only to show what
-- the paper claims. See refutation/ for the counterexample.
axiom zhu_lemma4_claim : ∀ (n : Nat),
  n > 0 →
  -- Paper claims at most n/2 non-isomorphic matchings to enumerate
  ∃ (bound : Nat), bound ≤ n / 2

-- Theorem 3: Claimed polynomial complexity
--
-- "Given the incidence matrix Cnm of a Γ digraph, the complexity of finding
--  a Hamiltonian cycle existing or not is O(n⁴)"
--
-- The claimed algorithm:
-- 1. Construct projector graph G (polynomial)
-- 2. Enumerate all n/2 non-isomorphic perfect matchings (INVALID: actually 2^(n/4))
-- 3. For each matching M, check if r(F⁻¹(M)) = n−1 (O(n³) each)
-- 4. Total: n/2 × O(n³) = O(n⁴) (INVALID due to step 2)

-- CLAIM (Theorem 3): The algorithm is polynomial
-- WARNING: This claim is INVALID because it depends on Lemma 4
axiom theorem3_polynomial_hcp : ∀ (D : GammaDigraph),
  ∃ (time : Nat → Nat), ∀ n, time n ≤ n ^ 4

-- Equations 10-11: Recursive matching enumeration
--
-- "M' = M(t) ⊗ Gt, if Gt is a cycle; M(t), otherwise"
-- "M(t+1) = M', if r(F⁻¹(M')) > r(F⁻¹(M(t))); M(t), otherwise"
--
-- NOTE: These recursive equations are underspecified:
-- - The ⊗ operation is not formally defined
-- - No proof of termination is provided
-- - No proof that all matchings are enumerated
-- - No complexity analysis is given

-- Cannot formalize equations 10-11: the ⊗ operation is undefined

-- Theorem 6: Extension to all digraphs with degree bound two
--
-- "The complexity of finding a Hamiltonian cycle existing or not in digraphs
--  with degree d+(v) ≤ 2 and d−(v) ≤ 2 is polynomial time."
--
-- The argument uses vertex splitting to reduce to Γ-digraphs.
-- This part of the argument is structurally sound, but depends on
-- the invalid Theorem 3.

-- CLAIM (Theorem 6): Extension to general degree-2 digraphs
-- This depends on Theorem 3 which is invalid
axiom theorem6_degree2_polynomial : ∀ (D : Digraph),
  -- If D has degree bound 2 (simplified)
  True →
  -- Then HCP is polynomial
  ∃ (time : Nat → Nat), ∀ n, time n ≤ (2 * n) ^ 4

-- Theorem 7: The P=NP conclusion
--
-- "P = NP"
--
-- "As the result of [Plesník 1978], the complexity of HCP in digraph with
--  bound two is NP-complete. According to theorem 6, the complexity of HCP
--  in digraph with bound two is also P, thus according to Cook's proposition,
--  P = NP."
--
-- NOTE: This conclusion is INVALID because Theorem 3 (and therefore Theorem 6)
-- depend on the incorrect Lemma 4.

-- The final (invalid) conclusion
-- WARNING: This does NOT follow because the proof chain is broken at Lemma 4
axiom theorem7_p_eq_np :
  -- HCP in degree-2 digraphs is NP-complete (Plesník 1978) - this is CORRECT
  True →
  -- HCP in degree-2 digraphs is in P (Theorem 6) - this is INVALID
  True →
  -- Therefore P = NP - this does NOT follow
  True

-- Summary of the proof structure
--
-- The proof chain is:
--   Theorem 1 (projector graph) ← VALID
--   Theorem 2 (HC ↔ matching)  ← VALID
--   Lemma 4 (counting)          ← INVALID (2^k ≠ 2k)
--   Theorem 3 (O(n⁴) algorithm) ← INVALID (depends on Lemma 4)
--   Theorem 6 (extension)        ← INVALID (depends on Theorem 3)
--   Theorem 7 (P=NP)            ← INVALID (depends on Theorem 6)
--
-- The error propagates from Lemma 4 through the rest of the proof.
-- See refutation/ for the formal refutation.

end ZhuProof
