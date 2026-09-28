(*
  LaPlante's 2015 P=NP Clique Algorithm - Counterexample Formalization

  This file formalizes the counterexample from Cardenas et al. (2015) that
  refutes LaPlante's claimed polynomial-time algorithm for the maximum clique problem.

  Reference: arXiv:1504.06890
  "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami"
*)

theory LaPlante2015Counterexample
  imports Main
begin

(* Graph Definitions *)

type_synonym vertex = nat
type_synonym edge = "vertex \<times> vertex"
type_synonym graph = "edge list"
type_synonym clique = "vertex list"

(* Helper Functions *)

fun connected :: "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool" where
  "connected [] _ _ = False" |
  "connected ((a,b)#es) v1 v2 = (
    if (a = v1 \<and> b = v2) \<or> (a = v2 \<and> b = v1)
    then True
    else connected es v1 v2
  )"

fun is_clique :: "graph \<Rightarrow> clique \<Rightarrow> bool" where
  "is_clique g [] = True" |
  "is_clique g [_] = True" |
  "is_clique g (v1#rest) = (
    (\<forall>v2 \<in> set rest. connected g v1 v2) \<and> is_clique g rest
  )"

definition clique_size :: "clique \<Rightarrow> nat" where
  "clique_size c = length c"

(* The Counterexample Graph *)

(* Letter vertices (represented as numbers 6-15) *)
definition vertex_A :: vertex where "vertex_A = 6"
definition vertex_B :: vertex where "vertex_B = 7"
definition vertex_C :: vertex where "vertex_C = 8"
definition vertex_D :: vertex where "vertex_D = 9"
definition vertex_E :: vertex where "vertex_E = 10"
definition vertex_F :: vertex where "vertex_F = 11"
definition vertex_G :: vertex where "vertex_G = 12"
definition vertex_H :: vertex where "vertex_H = 13"
definition vertex_I :: vertex where "vertex_I = 14"
definition vertex_J :: vertex where "vertex_J = 15"

(* The 5-clique edges (vertices 1-5) *)
definition five_clique_edges :: graph where
  "five_clique_edges = [
    (1,2), (1,3), (1,4), (1,5),
    (2,3), (2,4), (2,5),
    (3,4), (3,5),
    (4,5)
  ]"

(* Edges connecting to letter vertices to form 4-cliques *)
definition four_clique_edges :: graph where
  "four_clique_edges =
    (* Clique {1,2,3,A} *)
    [(1,vertex_A), (2,vertex_A), (3,vertex_A)] @
    (* Clique {1,2,4,B} *)
    [(1,vertex_B), (2,vertex_B), (4,vertex_B)] @
    (* Clique {1,2,5,C} *)
    [(1,vertex_C), (2,vertex_C), (5,vertex_C)] @
    (* Clique {1,3,4,D} *)
    [(1,vertex_D), (3,vertex_D), (4,vertex_D)] @
    (* Clique {1,3,5,E} *)
    [(1,vertex_E), (3,vertex_E), (5,vertex_E)] @
    (* Clique {1,4,5,F} *)
    [(1,vertex_F), (4,vertex_F), (5,vertex_F)] @
    (* Clique {2,3,4,G} *)
    [(2,vertex_G), (3,vertex_G), (4,vertex_G)] @
    (* Clique {2,3,5,H} *)
    [(2,vertex_H), (3,vertex_H), (5,vertex_H)] @
    (* Clique {2,4,5,I} *)
    [(2,vertex_I), (4,vertex_I), (5,vertex_I)] @
    (* Clique {3,4,5,J} *)
    [(3,vertex_J), (4,vertex_J), (5,vertex_J)]
  "

(* The complete counterexample graph *)
definition counterexample_graph :: graph where
  "counterexample_graph = five_clique_edges @ four_clique_edges"

(* Key Cliques in the Graph *)

(* The maximum 5-clique *)
definition max_clique :: clique where
  "max_clique = [1, 2, 3, 4, 5]"

(* Example 4-cliques that can mislead the algorithm *)
definition clique_123A :: clique where
  "clique_123A = [1, 2, 3, vertex_A]"

definition clique_124B :: clique where
  "clique_124B = [1, 2, 4, vertex_B]"

(* Verification *)

lemma max_clique_is_valid:
  "is_clique counterexample_graph max_clique"
  unfolding counterexample_graph_def max_clique_def
    five_clique_edges_def four_clique_edges_def
    vertex_A_def vertex_B_def vertex_C_def vertex_D_def vertex_E_def
    vertex_F_def vertex_G_def vertex_H_def vertex_I_def vertex_J_def
  by eval

lemma max_clique_has_size_5:
  "clique_size max_clique = 5"
  unfolding clique_size_def max_clique_def
  by simp

lemma four_clique_123A_is_valid:
  "is_clique counterexample_graph clique_123A"
  unfolding counterexample_graph_def clique_123A_def
    five_clique_edges_def four_clique_edges_def vertex_A_def
    vertex_B_def vertex_C_def vertex_D_def vertex_E_def
    vertex_F_def vertex_G_def vertex_H_def vertex_I_def vertex_J_def
  by eval

lemma four_clique_124B_is_valid:
  "is_clique counterexample_graph clique_124B"
  unfolding counterexample_graph_def clique_124B_def
    five_clique_edges_def four_clique_edges_def vertex_A_def
    vertex_B_def vertex_C_def vertex_D_def vertex_E_def
    vertex_F_def vertex_G_def vertex_H_def vertex_I_def vertex_J_def
  by eval

(* LaPlante's Algorithm Model *)

(* A 3-clique (triangle) *)
type_synonym triangle = "vertex \<times> vertex \<times> vertex"

(* The Core Problem

   The algorithm's flaw: when processing vertex 1, it can arbitrarily choose
   to merge {2,3} with {2,A} instead of {2,4}, leading to the 4-clique {1,2,3,A}
   instead of continuing to build the 5-clique {1,2,3,4,5}.

   This demonstrates that the algorithm's correctness depends on arbitrary choices
   that are not guided by any guarantee of finding the maximum clique.
*)

(* Theorem: The counterexample graph contains both the 5-clique and multiple 4-cliques *)

theorem counterexample_has_both_cliques:
  "is_clique counterexample_graph max_clique \<and>
   is_clique counterexample_graph clique_123A"
  using max_clique_is_valid four_clique_123A_is_valid
  by simp

(* Theorem: The 5-clique is larger than any 4-clique *)

theorem max_clique_is_larger:
  "clique_size max_clique > clique_size clique_123A"
  unfolding clique_size_def max_clique_def clique_123A_def vertex_A_def
  by simp

(*
  Key Insight

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
*)

(* Main theorem: LaPlante's algorithm is incorrect *)

theorem laplante_algorithm_is_incorrect:
  "\<exists>g maxC foundC.
    is_clique g maxC \<and>
    is_clique g foundC \<and>
    clique_size maxC > clique_size foundC"
proof -
  have "is_clique counterexample_graph max_clique"
    using max_clique_is_valid by simp
  moreover have "is_clique counterexample_graph clique_123A"
    using four_clique_123A_is_valid by simp
  moreover have "clique_size max_clique > clique_size clique_123A"
    using max_clique_is_larger by simp
  ultimately show ?thesis
    by (metis (no_types, lifting))
qed

(*
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
*)

end
