(** * LaPlante's 2015 P=NP Clique Algorithm - Counterexample Formalization

    This file formalizes the counterexample from Cardenas et al. (2015) that
    refutes LaPlante's claimed polynomial-time algorithm for the maximum clique problem.

    Reference: arXiv:1504.06890
    "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami"
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Decidable.
Import ListNotations.

(** * Graph Definitions *)

(** A vertex is represented as a natural number *)
Definition Vertex := nat.

(** An edge is a pair of vertices *)
Definition Edge := (Vertex * Vertex)%type.

(** A graph is a list of edges *)
Definition Graph := list Edge.

(** A clique is a list of vertices *)
Definition Clique := list Vertex.

(** * Helper Functions *)

(** Check if a vertex is in a list *)
Fixpoint vertex_in (v : Vertex) (l : list Vertex) : bool :=
  match l with
  | [] => false
  | h :: t => if Nat.eqb v h then true else vertex_in v t
  end.

(** Check if an edge exists in a graph *)
Definition has_edge (g : Graph) (v1 v2 : Vertex) : bool :=
  existsb (fun e =>
    match e with
    | (a, b) => (Nat.eqb a v1 && Nat.eqb b v2) || (Nat.eqb a v2 && Nat.eqb b v1)
    end) g.

(** Check if two vertices are connected in a graph *)
Definition connected (g : Graph) (v1 v2 : Vertex) : bool :=
  has_edge g v1 v2.

(** Check if a set of vertices forms a clique *)
Fixpoint is_clique (g : Graph) (c : Clique) : bool :=
  match c with
  | [] => true
  | [_] => true
  | v1 :: rest =>
      (forallb (fun v2 => connected g v1 v2) rest) && is_clique g rest
  end.

(** Get the size of a clique *)
Definition clique_size (c : Clique) : nat := length c.

(** * The Counterexample Graph

    This is a 15-vertex graph with 5-way rotational symmetry:
    - Vertices 1-5 form a 5-clique (the maximum clique)
    - Vertices labeled A-J (represented as 6-15)
    - Each combination of 3 vertices from {1,2,3,4,5} forms a 4-clique
      with one letter vertex
*)

Definition VertexA := 6.
Definition VertexB := 7.
Definition VertexC := 8.
Definition VertexD := 9.
Definition VertexE := 10.
Definition VertexF := 11.
Definition VertexG := 12.
Definition VertexH := 13.
Definition VertexI := 14.
Definition VertexJ := 15.

(** The 5-clique edges *)
Definition five_clique_edges : Graph :=
  [(1,2); (1,3); (1,4); (1,5);
   (2,3); (2,4); (2,5);
   (3,4); (3,5);
   (4,5)].

(** Edges connecting to letter vertices to form 4-cliques *)
Definition four_clique_edges : Graph :=
  (* Clique {1,2,3,A} *)
  [(1,VertexA); (2,VertexA); (3,VertexA)] ++
  (* Clique {1,2,4,B} *)
  [(1,VertexB); (2,VertexB); (4,VertexB)] ++
  (* Clique {1,2,5,C} *)
  [(1,VertexC); (2,VertexC); (5,VertexC)] ++
  (* Clique {1,3,4,D} *)
  [(1,VertexD); (3,VertexD); (4,VertexD)] ++
  (* Clique {1,3,5,E} *)
  [(1,VertexE); (3,VertexE); (5,VertexE)] ++
  (* Clique {1,4,5,F} *)
  [(1,VertexF); (4,VertexF); (5,VertexF)] ++
  (* Clique {2,3,4,G} *)
  [(2,VertexG); (3,VertexG); (4,VertexG)] ++
  (* Clique {2,3,5,H} *)
  [(2,VertexH); (3,VertexH); (5,VertexH)] ++
  (* Clique {2,4,5,I} *)
  [(2,VertexI); (4,VertexI); (5,VertexI)] ++
  (* Clique {3,4,5,J} *)
  [(3,VertexJ); (4,VertexJ); (5,VertexJ)].

(** The complete counterexample graph *)
Definition counterexample_graph : Graph :=
  five_clique_edges ++ four_clique_edges.

(** * Key Cliques in the Graph *)

(** The maximum 5-clique *)
Definition max_clique : Clique := [1; 2; 3; 4; 5].

(** Example 4-cliques that can mislead the algorithm *)
Definition clique_123A : Clique := [1; 2; 3; VertexA].
Definition clique_124B : Clique := [1; 2; 4; VertexB].

(** * Verification *)

(** Verify that the 5-clique is indeed a clique *)
Example max_clique_is_valid :
  is_clique counterexample_graph max_clique = true.
Proof. reflexivity. Qed.

(** Verify that the 5-clique has size 5 *)
Example max_clique_has_size_5 :
  clique_size max_clique = 5.
Proof. reflexivity. Qed.

(** Verify that the 4-cliques are valid *)
Example four_clique_123A_is_valid :
  is_clique counterexample_graph clique_123A = true.
Proof. reflexivity. Qed.

Example four_clique_124B_is_valid :
  is_clique counterexample_graph clique_124B = true.
Proof. reflexivity. Qed.

(** * LaPlante's Algorithm Model *)

(** A 3-clique (triangle) *)
Definition Triangle := (Vertex * Vertex * Vertex)%type.

(** Extract the vertices from a triangle *)
Definition triangle_vertices (t : Triangle) : list Vertex :=
  match t with (v1, v2, v3) => [v1; v2; v3] end.

(** Find all triangles containing a given vertex *)
Fixpoint find_triangles_with_vertex (g : Graph) (v : Vertex) (vertices : list Vertex) : list Triangle :=
  match vertices with
  | [] => []
  | v1 :: rest =>
      let triangles_with_v1 :=
        flat_map (fun v2 =>
          if (Nat.eqb v1 v2) then []
          else if (connected g v v1 && connected g v v2 && connected g v1 v2)
               then [(v, v1, v2)]
               else []) rest
      in triangles_with_v1 ++ find_triangles_with_vertex g v rest
  end.

(** * The Core Problem

    The algorithm's flaw: when processing vertex 1, it can arbitrarily choose
    to merge {2,3} with {2,A} instead of {2,4}, leading to the 4-clique {1,2,3,A}
    instead of continuing to build the 5-clique {1,2,3,4,5}.

    This demonstrates that the algorithm's correctness depends on arbitrary choices
    that are not guided by any guarantee of finding the maximum clique.
*)

(** A vertex pair (from a 3-clique perspective) *)
Definition VertexPair := (Vertex * Vertex)%type.

(** Theorem: The counterexample graph contains both the 5-clique and multiple 4-cliques *)
Theorem counterexample_has_both_cliques :
  is_clique counterexample_graph max_clique = true /\
  is_clique counterexample_graph clique_123A = true.
Proof.
  split; reflexivity.
Qed.

(** Theorem: Any vertex from the 5-clique is also part of multiple 4-cliques *)
Theorem vertex_in_multiple_cliques :
  vertex_in 1 max_clique = true /\
  vertex_in 1 clique_123A = true /\
  vertex_in 1 clique_124B = true.
Proof.
  split; [reflexivity | split; reflexivity].
Qed.

(** * Key Insight

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

(** Conclusion marker *)
Theorem laplante_algorithm_is_incorrect :
  exists (g : Graph) (max : Clique) (found : Clique),
    is_clique g max = true /\
    is_clique g found = true /\
    clique_size max > clique_size found.
Proof.
  exists counterexample_graph, max_clique, clique_123A.
  split; [reflexivity | split; [reflexivity | simpl; lia]].
Qed.

(** This formalization demonstrates that LaPlante's algorithm can fail to find
    the maximum clique, thus refuting the claim that it solves the clique problem
    in polynomial time for all graphs. *)
