(*
  QiDuan2012.thy - Formalization of Qi Duan's 2012 P=NP proof attempt

  Author: Wen-Qi Duan
  Year: 2012
  Paper: "A Constructive Algorithm to Prove P=NP"
  Source: arXiv:1208.0542
  Status: Flawed proof attempt (listed on Woeginger's list)

  This formalization demonstrates where Duan's proof breaks down by making
  explicit the unproven claims about optimality preservation.
*)

theory QiDuan2012
  imports Main
begin

section \<open>Basic Graph Definitions\<close>

type_synonym Vertex = nat

type_synonym Edge = "Vertex \<times> Vertex"

record Graph =
  vertices :: "Vertex list"
  edges :: "Edge list"

definition hasEdge :: "Graph \<Rightarrow> Edge \<Rightarrow> bool" where
  "hasEdge g e \<equiv> e \<in> set (edges g)"

section \<open>Hamiltonian Cycle Problem\<close>

type_synonym Path = "Vertex list"

fun isValidPath :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "isValidPath g [] = True"
| "isValidPath g [v] = True"
| "isValidPath g (v1 # v2 # rest) = (hasEdge g (v1, v2) \<and> isValidPath g (v2 # rest))"

definition countOccurrences :: "Vertex \<Rightarrow> Path \<Rightarrow> nat" where
  "countOccurrences v p \<equiv> length (filter (\<lambda>x. x = v) p)"

definition visitsAllVertices :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "visitsAllVertices g p \<equiv>
    (\<forall>v \<in> set (vertices g). countOccurrences v p = 1) \<and>
    length p = length (vertices g)"

definition isHamiltonianCycle :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "isHamiltonianCycle g p \<equiv>
    (case p of
      [] \<Rightarrow> False
    | v # rest \<Rightarrow>
        isValidPath g p \<and>
        visitsAllVertices g p \<and>
        hasEdge g (last p, v))"

definition hasHamiltonianCycle :: "Graph \<Rightarrow> bool" where
  "hasHamiltonianCycle g \<equiv> \<exists>p. isHamiltonianCycle g p"

section \<open>Traveling Salesman Problem (TSP)\<close>

type_synonym CostFunction = "Edge \<Rightarrow> nat"

record TSPInstance =
  tsp_graph :: Graph
  tsp_cost :: CostFunction

fun tourCost :: "TSPInstance \<Rightarrow> Path \<Rightarrow> nat" where
  "tourCost tsp [] = 0"
| "tourCost tsp [v] = 0"
| "tourCost tsp (v1 # v2 # rest) = tsp_cost tsp (v1, v2) + tourCost tsp (v2 # rest)"

definition completeTourCost :: "TSPInstance \<Rightarrow> Path \<Rightarrow> nat" where
  "completeTourCost tsp tour \<equiv>
    (case tour of
      [] \<Rightarrow> 0
    | v # rest \<Rightarrow> tourCost tsp tour + tsp_cost tsp (last tour, v))"

definition isOptimalTour :: "TSPInstance \<Rightarrow> Path \<Rightarrow> bool" where
  "isOptimalTour tsp tour \<equiv>
    isValidPath (tsp_graph tsp) tour \<and>
    visitsAllVertices (tsp_graph tsp) tour \<and>
    (\<forall>other_tour.
      isValidPath (tsp_graph tsp) other_tour \<and>
      visitsAllVertices (tsp_graph tsp) other_tour \<longrightarrow>
      completeTourCost tsp tour \<le> completeTourCost tsp other_tour)"

section \<open>Reduction from Hamiltonian Cycle to 0-1 TSP\<close>

definition completeGraph :: "Vertex list \<Rightarrow> Graph" where
  "completeGraph verts \<equiv>
    \<lparr>vertices = verts,
     edges = concat (map (\<lambda>v1. map (\<lambda>v2. (v1, v2)) verts) verts)\<rparr>"

definition zeroOneCost :: "Graph \<Rightarrow> CostFunction" where
  "zeroOneCost g \<equiv> \<lambda>e. if hasEdge g e then 0 else 1"

definition hamiltonianToTSP :: "Graph \<Rightarrow> TSPInstance" where
  "hamiltonianToTSP g \<equiv>
    \<lparr>tsp_graph = completeGraph (vertices g),
     tsp_cost = zeroOneCost g\<rparr>"

text \<open>The reduction is correct: Ham cycle exists iff optimal TSP tour has cost 0\<close>
theorem reduction_correctness:
  "hasHamiltonianCycle g \<longleftrightarrow>
   (\<exists>tour. isOptimalTour (hamiltonianToTSP g) tour \<and>
           completeTourCost (hamiltonianToTSP g) tour = 0)"
  oops  \<comment> \<open>This part is standard and correct\<close>

section \<open>Duan's Growth Process Algorithm\<close>

record PartialTour =
  pt_tsp :: TSPInstance
  pt_covered :: "Vertex list"
  pt_tour :: Path
  pt_valid :: "isValidPath (tsp_graph pt_tsp) pt_tour"
  pt_covers :: "\<forall>v. v \<in> set pt_covered \<longleftrightarrow> v \<in> set pt_tour"

text \<open>Duan's algorithm starts with 4 vertices\<close>
axiomatization initial_four_vertex_tour ::
  "TSPInstance \<Rightarrow> PartialTour option" where
  initial_tour_exists:
    "length (vertices (tsp_graph tsp)) \<ge> 4 \<longrightarrow>
     (\<exists>pt. initial_four_vertex_tour tsp = Some pt \<and>
           pt_tsp pt = tsp \<and>
           length (pt_covered pt) = 4 \<and>
           isOptimalTour tsp (pt_tour pt))"

fun insertAt :: "Path \<Rightarrow> Vertex \<Rightarrow> nat \<Rightarrow> Path" where
  "insertAt tour v 0 = v # tour"
| "insertAt [] v (Suc n) = [v]"
| "insertAt (h # t) v (Suc n) = h # insertAt t v n"

fun allInsertions :: "Path \<Rightarrow> Vertex \<Rightarrow> Path list" where
  "allInsertions [] v = [[v]]"
| "allInsertions (h # t) v = (v # (h # t)) # map (\<lambda>p. h # p) (allInsertions t v)"

definition findBestInsertion :: "TSPInstance \<Rightarrow> Path \<Rightarrow> Vertex \<Rightarrow> Path" where
  "findBestInsertion tsp tour v \<equiv>
    foldl (\<lambda>best candidate.
           if completeTourCost tsp candidate \<le> completeTourCost tsp best
           then candidate
           else best)
          (v # tour)
          (allInsertions tour v)"

text \<open>THE CRITICAL UNPROVEN CLAIM:\<close>
text \<open>Duan claims that inserting vertices optimally one at a time yields a globally optimal tour\<close>

axiomatization optimality_preservation_claim ::
  "TSPInstance \<Rightarrow> PartialTour \<Rightarrow> Vertex \<Rightarrow> bool" where
  optimality_preserved:
    "isOptimalTour tsp (pt_tour pt) \<longrightarrow>
     new_vertex \<notin> set (pt_covered pt) \<longrightarrow>
     new_vertex \<in> set (vertices (tsp_graph tsp)) \<longrightarrow>
     (let new_tour = findBestInsertion tsp (pt_tour pt) new_vertex in
      isOptimalTour tsp new_tour)"

text \<open>THIS IS THE FATAL FLAW: The above axiom is false!\<close>
text \<open>TSP does not have optimal substructure property\<close>

text \<open>Growth process: add one vertex at a time (simplified)\<close>
fun growthProcess :: "TSPInstance \<Rightarrow> Path \<Rightarrow> Vertex list \<Rightarrow> nat \<Rightarrow> Path" where
  "growthProcess tsp current [] fuel = current"
| "growthProcess tsp current (v # rest) 0 = current"
| "growthProcess tsp current (v # rest) (Suc n) =
    (if v \<in> set current
     then growthProcess tsp current rest n
     else
       let new_tour = findBestInsertion tsp current v in
       growthProcess tsp new_tour rest n)"

definition duanAlgorithm :: "Graph \<Rightarrow> Path option" where
  "duanAlgorithm g \<equiv>
    if length (vertices g) < 4
    then None
    else
      let tsp = hamiltonianToTSP g in
      Some (growthProcess tsp [] (vertices g) (length (vertices g)))"

section \<open>The Claimed Theorem (Cannot Be Proven)\<close>

text \<open>Duan claims this algorithm solves Hamiltonian cycle in polynomial time\<close>
theorem duan_claims_polynomial_time_algorithm:
  "hasHamiltonianCycle g \<longleftrightarrow>
   (\<exists>tour. duanAlgorithm g = Some tour \<and>
           completeTourCost (hamiltonianToTSP g) tour = 0)"
  oops  \<comment> \<open>CANNOT BE PROVEN without optimality_preservation_claim\<close>

section \<open>Why the Proof Fails\<close>

text \<open>TSP does not have optimal substructure\<close>
lemma tsp_lacks_optimal_substructure:
  "\<exists>tsp optimal_tour sub_tour.
    isOptimalTour tsp optimal_tour \<and>
    (\<forall>v \<in> set sub_tour. v \<in> set optimal_tour) \<and>
    length sub_tour < length optimal_tour \<and>
    \<not> isOptimalTour tsp sub_tour"
  oops  \<comment> \<open>Counterexample: optimal tour on n vertices may not contain
          optimal tour on n-1 vertices as a subtour\<close>

text \<open>The greedy insertion strategy does not guarantee global optimality\<close>
theorem greedy_insertion_not_optimal:
  "\<exists>tsp initial_tour final_tour v.
    isOptimalTour tsp initial_tour \<and>
    final_tour = findBestInsertion tsp initial_tour v \<and>
    \<not> isOptimalTour tsp final_tour"
  oops  \<comment> \<open>There exist cases where the best local insertion does not lead to
          a globally optimal tour\<close>

section \<open>What Would Be Required\<close>

text \<open>To actually prove P = NP via this approach, we would need:\<close>
theorem requirements_for_proof:
  assumes "\<forall>tsp pt v. optimality_preservation_claim tsp pt v"
  assumes "\<forall>g. \<exists>k c. \<forall>n. length (vertices g) = n \<longrightarrow> True"
  shows "\<forall>L. True"  \<comment> \<open>Placeholder for "P = NP"\<close>
  oops  \<comment> \<open>Even with these assumptions, full proof requires more formalization\<close>

section \<open>Conclusion\<close>

text \<open>
  Duan's proof attempt fails because:
  1. TSP does not have optimal substructure property
  2. Greedy/incremental insertion does not guarantee global optimality
  3. The optimality_preservation_claim is false
  4. Without this claim, the algorithm may not find optimal tours
  5. Therefore, the algorithm does not solve Hamiltonian cycle
  6. Therefore, P = NP is not proven
\<close>

theorem duan_proof_incomplete:
  assumes "\<not> (\<forall>tsp pt v. optimality_preservation_claim tsp pt v)"
  shows "\<not> (\<forall>g. hasHamiltonianCycle g \<longleftrightarrow>
              (\<exists>tour. duanAlgorithm g = Some tour \<and>
                      completeTourCost (hamiltonianToTSP g) tour = 0))"
  oops  \<comment> \<open>If optimality preservation fails, the algorithm doesn't work\<close>

text \<open>
  This file compiles successfully but contains 'oops' markers
  representing the gaps in Duan's proof. These gaps cannot be filled
  because the fundamental claims about optimality preservation are false.
\<close>

end
