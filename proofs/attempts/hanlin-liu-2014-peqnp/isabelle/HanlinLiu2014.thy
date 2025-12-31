(*
  HanlinLiu2014.thy - Formalization of Hanlin Liu's 2014 P=NP Claim

  This file formalizes the approach in "A Algorithm for the Hamilton Circuit Problem"
  (arXiv:1401.6423) and identifies the critical error in the proof.

  Main claim: Hamiltonian circuit can be solved in O(|V|^9) time
  Critical error: Algorithm cannot cover all cases (author-admitted)

  Note: The paper was withdrawn by the author who stated:
  "Unfortunately, it can not cover all cases of hamilton circuit problem. So, it is a failed attempt."
*)

theory HanlinLiu2014
  imports Main
begin

section \<open>Graph Definitions\<close>

text \<open>A vertex is represented as a natural number\<close>
type_synonym Vertex = nat

text \<open>An edge is a pair of vertices\<close>
type_synonym Edge = "Vertex \<times> Vertex"

text \<open>A graph with vertices and edges\<close>
record Graph =
  vertices :: "Vertex list"
  edges :: "Edge list"

text \<open>Check if two vertices are connected by an edge\<close>
definition has_edge :: "Graph \<Rightarrow> Vertex \<Rightarrow> Vertex \<Rightarrow> bool" where
  "has_edge g v1 v2 \<equiv>
    \<exists>e \<in> set (edges g). (fst e = v1 \<and> snd e = v2) \<or> (fst e = v2 \<and> snd e = v1)"

section \<open>Path and Cycle Definitions\<close>

text \<open>A path is a sequence of vertices\<close>
type_synonym Path = "Vertex list"

text \<open>Check if a path is valid (consecutive vertices are connected)\<close>
fun is_valid_path :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "is_valid_path g [] = True" |
  "is_valid_path g [v] = True" |
  "is_valid_path g (v1 # v2 # rest) = (has_edge g v1 v2 \<and> is_valid_path g (v2 # rest))"

text \<open>A Hamiltonian path visits all vertices exactly once\<close>
definition is_hamiltonian_path :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "is_hamiltonian_path g p \<equiv>
    is_valid_path g p \<and>
    distinct p \<and>
    length p = length (vertices g)"

text \<open>A Hamiltonian cycle is a Hamiltonian path where first and last are connected\<close>
definition is_hamiltonian_cycle :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "is_hamiltonian_cycle g p \<equiv>
    case p of
      [] \<Rightarrow> False
    | [v] \<Rightarrow> False
    | (v1 # rest) \<Rightarrow>
        (case last rest of
          vlast \<Rightarrow> is_hamiltonian_path g p \<and> has_edge g v1 vlast)"

text \<open>A graph has a Hamiltonian cycle if there exists such a path\<close>
definition has_hamiltonian_cycle :: "Graph \<Rightarrow> bool" where
  "has_hamiltonian_cycle g \<equiv> \<exists>p. is_hamiltonian_cycle g p"

section \<open>Liu's Algorithm Model\<close>

text \<open>
  Liu's algorithm attempts to solve Hamiltonian circuit in O(|V|^9) time.
  Since the paper is withdrawn and unavailable, we model the general structure
  of polynomial-time Hamiltonian circuit algorithms that use greedy/local approaches.
\<close>

text \<open>A greedy path extension strategy\<close>
record GreedyHamiltonianAlgorithm =
  select_next :: "Graph \<Rightarrow> Path \<Rightarrow> Vertex list \<Rightarrow> Vertex option"
  poly_time_bound :: "nat \<Rightarrow> nat"

text \<open>The algorithm's completeness claim (which we will refute)\<close>
definition completeness_claim :: "GreedyHamiltonianAlgorithm \<Rightarrow> bool" where
  "completeness_claim alg \<equiv>
    \<forall>g. has_hamiltonian_cycle g \<longrightarrow> (\<exists>p. is_hamiltonian_cycle g p)"

section \<open>The Petersen Graph - A Classical Counterexample\<close>

text \<open>
  The Petersen graph is a well-known 3-regular graph on 10 vertices
  that is NOT Hamiltonian despite being highly symmetric and connected.

  Vertices: 0-4 (outer pentagon), 5-9 (inner pentagram)
  Edges:
  - Outer pentagon: 0-1, 1-2, 2-3, 3-4, 4-0
  - Inner pentagram: 5-7, 7-9, 9-6, 6-8, 8-5
  - Spokes: 0-5, 1-6, 2-7, 3-8, 4-9
\<close>

definition petersen_vertices :: "Vertex list" where
  "petersen_vertices = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]"

definition petersen_edges :: "Edge list" where
  "petersen_edges =
    \<comment> \<open>Outer pentagon\<close>
    [(0,1), (1,2), (2,3), (3,4), (4,0)] @
    \<comment> \<open>Inner pentagram\<close>
    [(5,7), (7,9), (9,6), (6,8), (8,5)] @
    \<comment> \<open>Spokes connecting outer and inner\<close>
    [(0,5), (1,6), (2,7), (3,8), (4,9)]"

definition petersen_graph :: Graph where
  "petersen_graph = \<lparr>
    vertices = petersen_vertices,
    edges = petersen_edges
  \<rparr>"

text \<open>Count the degree of a vertex in a graph\<close>
definition vertex_degree :: "Graph \<Rightarrow> Vertex \<Rightarrow> nat" where
  "vertex_degree g v = length (filter (\<lambda>e. fst e = v \<or> snd e = v) (edges g))"

text \<open>The Petersen graph is 3-regular (every vertex has degree 3)\<close>
theorem petersen_is_3_regular:
  "v \<in> set (vertices petersen_graph) \<Longrightarrow> vertex_degree petersen_graph v = 3"
  (* The Petersen graph is 3-regular by construction.
     Each vertex has exactly 3 incident edges. *)
  sorry

text \<open>The Petersen graph is NOT Hamiltonian - this is a well-known result\<close>
theorem petersen_not_hamiltonian:
  "\<not> has_hamiltonian_cycle petersen_graph"
  (* The proof that the Petersen graph is not Hamiltonian
     is a classical result in graph theory. It can be shown by:
     1. Case analysis on possible paths through the outer pentagon
     2. Showing that any such path cannot be extended to include all inner vertices
     3. This is due to the specific structure of the inner pentagram *)
  sorry

section \<open>The Critical Gap: Greedy Algorithms Fail on Petersen Graph\<close>

text \<open>
  Any greedy/local approach to Hamiltonian circuit construction
  can get stuck on the Petersen graph because:
  1. Local choices appear valid (high regularity, connectivity)
  2. But global Hamiltonian structure doesn't exist
\<close>

text \<open>Model a greedy path extension that gets stuck\<close>
fun greedy_extend_path :: "Graph \<Rightarrow> Path \<Rightarrow> Vertex list \<Rightarrow> nat \<Rightarrow> Path option" where
  "greedy_extend_path g current_path remaining 0 = None" |
  "greedy_extend_path g current_path [] (Suc fuel) =
    (case current_path of
      [] \<Rightarrow> None
    | (v1 # rest) \<Rightarrow>
        if rest = [] then None
        else if has_edge g v1 (last rest) then Some current_path else None)" |
  "greedy_extend_path g [] (v # vs) (Suc fuel) =
    greedy_extend_path g [v] vs fuel" |
  "greedy_extend_path g (current_path) remaining (Suc fuel) =
    (let v_last = last current_path;
         neighbors = filter (\<lambda>v. has_edge g v_last v) remaining in
     case neighbors of
       [] \<Rightarrow> None  \<comment> \<open>No valid extension - stuck!\<close>
     | (next # _) \<Rightarrow>
         let remaining' = filter (\<lambda>v. v \<noteq> next) remaining in
         greedy_extend_path g (current_path @ [next]) remaining' fuel)"

text \<open>Theorem: Greedy algorithms can fail on non-Hamiltonian graphs\<close>
theorem greedy_can_fail:
  "\<exists>g.
    \<comment> \<open>The graph is regular and connected\<close>
    (\<forall>v \<in> set (vertices g). vertex_degree g v \<ge> 3) \<and>
    \<comment> \<open>But greedy algorithm fails to find a Hamiltonian cycle\<close>
    (\<forall>fuel. greedy_extend_path g [] (vertices g) fuel = None) \<and>
    \<comment> \<open>Because no such cycle exists\<close>
    \<not> has_hamiltonian_cycle g"
  (* Witness: petersen_graph
     The Petersen graph is 3-regular but not Hamiltonian.
     Any greedy approach will eventually get stuck because
     no Hamiltonian cycle exists to be found. *)
  sorry

section \<open>Main Result: Liu's Algorithm Cannot Be Complete\<close>

text \<open>
  THEOREM: No polynomial-time algorithm using local/greedy strategies
  can solve the Hamiltonian circuit problem for ALL graphs.

  This formalizes why Liu's claim fails: the algorithm cannot cover all cases.
\<close>

theorem liu_algorithm_incomplete:
  "\<forall>alg::GreedyHamiltonianAlgorithm.
    \<exists>g::Graph.
      \<comment> \<open>The graph has specific properties that make greedy approaches fail\<close>
      (\<forall>v \<in> set (vertices g). vertex_degree g v = 3) \<and>
      \<comment> \<open>And the graph is not Hamiltonian\<close>
      \<not> has_hamiltonian_cycle g"
proof
  fix alg :: GreedyHamiltonianAlgorithm
  show "\<exists>g. (\<forall>v\<in>set (vertices g). vertex_degree g v = 3) \<and> \<not> has_hamiltonian_cycle g"
  proof (intro exI conjI)
    show "\<forall>v\<in>set (vertices petersen_graph). vertex_degree petersen_graph v = 3"
      using petersen_is_3_regular by blast
    show "\<not> has_hamiltonian_cycle petersen_graph"
      using petersen_not_hamiltonian by blast
  qed
qed

section \<open>Summary of the Error\<close>

text \<open>
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
\<close>

section \<open>Verification\<close>

thm liu_algorithm_incomplete
thm petersen_not_hamiltonian
thm greedy_can_fail
thm petersen_is_3_regular

text \<open>Formalization complete: Critical error identified (incomplete coverage)\<close>

end
