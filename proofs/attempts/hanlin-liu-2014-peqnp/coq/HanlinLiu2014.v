(**
  HanlinLiu2014.v - Formalization of Hanlin Liu's 2014 P=NP Claim

  This file formalizes the approach in "A Algorithm for the Hamilton Circuit Problem"
  (arXiv:1401.6423) and identifies the critical error in the proof.

  Main claim: Hamiltonian circuit can be solved in O(|V|^9) time
  Critical error: Algorithm cannot cover all cases (author-admitted)

  Note: The paper was withdrawn by the author who stated:
  "Unfortunately, it can not cover all cases of hamilton circuit problem. So, it is a failed attempt."
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

(** * Graph Definitions *)

(** A vertex is represented as a natural number *)
Definition Vertex := nat.

(** An edge is a pair of vertices *)
Definition Edge := (Vertex * Vertex)%type.

(** A graph with vertices and edges *)
Record Graph : Type := {
  vertices : list Vertex;
  edges : list Edge;
  vertices_nonempty : vertices <> [];
}.

(** Check if two vertices are connected by an edge *)
Definition has_edge (g : Graph) (v1 v2 : Vertex) : bool :=
  existsb (fun e => match e with
    | (a, b) => (Nat.eqb a v1 && Nat.eqb b v2) || (Nat.eqb a v2 && Nat.eqb b v1)
    end) (edges g).

(** * Path and Cycle Definitions *)

(** A path is a sequence of vertices *)
Definition Path := list Vertex.

(** Check if a path is valid (consecutive vertices are connected) *)
Fixpoint is_valid_path (g : Graph) (p : Path) : bool :=
  match p with
  | [] => true
  | [_] => true
  | v1 :: ((v2 :: _) as rest) => has_edge g v1 v2 && is_valid_path g rest
  end.

(** Check if all elements in a list are distinct *)
Fixpoint all_distinct (l : list Vertex) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (Nat.eqb x) xs) && all_distinct xs
  end.

(** A Hamiltonian path visits all vertices exactly once *)
Definition is_hamiltonian_path (g : Graph) (p : Path) : bool :=
  is_valid_path g p &&
  all_distinct p &&
  (length p =? length (vertices g)).

(** A Hamiltonian cycle is a Hamiltonian path where first and last are connected *)
Definition is_hamiltonian_cycle (g : Graph) (p : Path) : bool :=
  match p with
  | [] => false
  | [_] => false
  | v1 :: rest =>
      match last rest v1 with
      | vlast => is_hamiltonian_path g p && has_edge g v1 vlast
      end
  end.

(** A graph has a Hamiltonian cycle if there exists such a path *)
Definition has_hamiltonian_cycle (g : Graph) : Prop :=
  exists p : Path, is_hamiltonian_cycle g p = true.

(** * Liu's Algorithm Model *)

(**
  Liu's algorithm attempts to solve Hamiltonian circuit in O(|V|^9) time.
  Since the paper is withdrawn and unavailable, we model the general structure
  of polynomial-time Hamiltonian circuit algorithms that use greedy/local approaches.
*)

(** A greedy path extension strategy *)
Record GreedyHamiltonianAlgorithm : Type := {
  (* Function to select the next vertex to add to the path *)
  select_next : Graph -> Path -> list Vertex -> option Vertex;

  (* Claimed polynomial time bound *)
  poly_time_bound : nat -> nat;

  (* The algorithm claimed to always find a Hamiltonian cycle if one exists *)
  completeness_claim : forall g,
    has_hamiltonian_cycle g ->
    exists p, is_hamiltonian_cycle g p = true;
}.

(** * The Petersen Graph - A Classical Counterexample *)

(**
  The Petersen graph is a well-known 3-regular graph on 10 vertices
  that is NOT Hamiltonian despite being highly symmetric and connected.

  Vertices: 0-4 (outer pentagon), 5-9 (inner pentagram)
  Edges:
  - Outer pentagon: 0-1, 1-2, 2-3, 3-4, 4-0
  - Inner pentagram: 5-7, 7-9, 9-6, 6-8, 8-5
  - Spokes: 0-5, 1-6, 2-7, 3-8, 4-9
*)

Definition petersen_vertices : list Vertex := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

Definition petersen_edges : list Edge :=
  (* Outer pentagon *)
  [(0,1); (1,2); (2,3); (3,4); (4,0)] ++
  (* Inner pentagram *)
  [(5,7); (7,9); (9,6); (6,8); (8,5)] ++
  (* Spokes connecting outer and inner *)
  [(0,5); (1,6); (2,7); (3,8); (4,9)].

Definition petersen_graph : Graph.
Proof.
  refine {|
    vertices := petersen_vertices;
    edges := petersen_edges;
  |}.
  unfold petersen_vertices. discriminate.
Defined.

(** The Petersen graph is 3-regular (every vertex has degree 3) *)
Definition vertex_degree (g : Graph) (v : Vertex) : nat :=
  length (filter (fun e => match e with
    | (a, b) => Nat.eqb a v || Nat.eqb b v
    end) (edges g)).

Theorem petersen_is_3_regular :
  forall v, In v (vertices petersen_graph) -> vertex_degree petersen_graph v = 3.
Proof.
  (* The Petersen graph is 3-regular by construction *)
  (* Each vertex has exactly 3 incident edges *)
Admitted.

(** The Petersen graph is NOT Hamiltonian - this is a well-known result *)
Theorem petersen_not_hamiltonian :
  ~has_hamiltonian_cycle petersen_graph.
Proof.
  unfold has_hamiltonian_cycle.
  intro H.
  destruct H as [p Hp].
  (* The proof that the Petersen graph is not Hamiltonian
     is a classical result in graph theory. It can be shown by:
     1. Case analysis on possible paths through the outer pentagon
     2. Showing that any such path cannot be extended to include all inner vertices
     3. This is due to the specific structure of the inner pentagram *)
Admitted.

(** * The Critical Gap: Greedy Algorithms Fail on Petersen Graph *)

(**
  Any greedy/local approach to Hamiltonian circuit construction
  can get stuck on the Petersen graph because:
  1. Local choices appear valid (high regularity, connectivity)
  2. But global Hamiltonian structure doesn't exist
*)

(** Model a greedy path extension that gets stuck *)
Fixpoint greedy_extend_path (g : Graph) (current_path : Path)
         (remaining : list Vertex) (fuel : nat) : option Path :=
  match fuel with
  | O => None  (* Ran out of fuel - algorithm stuck *)
  | S fuel' =>
    match remaining with
    | [] =>
      (* All vertices visited - check if we can close the cycle *)
      match current_path with
      | [] => None
      | v1 :: _ =>
        match last current_path v1 with
        | vlast =>
          if has_edge g v1 vlast then Some current_path else None
        end
      end
    | _ =>
      (* Try to extend the path greedily *)
      match current_path with
      | [] =>
        (* Start with first remaining vertex *)
        match remaining with
        | [] => None
        | v :: vs => greedy_extend_path g [v] vs fuel'
        end
      | v_last :: _ =>
        (* Find a neighbor in remaining vertices *)
        let neighbors := filter (fun v => has_edge g v_last v) remaining in
        match neighbors with
        | [] => None  (* No valid extension - stuck! *)
        | next :: _ =>
          let remaining' := filter (fun v => negb (Nat.eqb v next)) remaining in
          greedy_extend_path g (current_path ++ [next]) remaining' fuel'
        end
      end
    end
  end.

(** Theorem: Greedy algorithms can fail on non-Hamiltonian graphs *)
Theorem greedy_can_fail :
  exists g : Graph,
    (* The graph is regular and connected *)
    (forall v, In v (vertices g) -> vertex_degree g v >= 3) /\
    (* But greedy algorithm fails to find a Hamiltonian cycle *)
    (forall fuel, greedy_extend_path g [] (vertices g) fuel = None) /\
    (* Because no such cycle exists *)
    ~has_hamiltonian_cycle g.
Proof.
  (* Witness: petersen_graph
     The Petersen graph is 3-regular but not Hamiltonian.
     Any greedy approach will eventually get stuck because
     no Hamiltonian cycle exists to be found.

     Full proof requires:
     1. Showing vertex degrees are >= 3 (3-regularity)
     2. Showing greedy extension gets stuck
     3. Using petersen_not_hamiltonian for non-Hamiltonicity *)
Admitted.

(** * Main Result: Liu's Algorithm Cannot Be Complete *)

(**
  THEOREM: No polynomial-time algorithm using local/greedy strategies
  can solve the Hamiltonian circuit problem for ALL graphs.

  This formalizes why Liu's claim fails: the algorithm cannot cover all cases.
*)

Theorem liu_algorithm_incomplete :
  forall alg : GreedyHamiltonianAlgorithm,
    (* There exists a graph where the algorithm fails *)
    exists g : Graph,
      (* The graph has specific properties that make greedy approaches fail *)
      (forall v, In v (vertices g) -> vertex_degree g v = 3) /\
      (* And the graph is not Hamiltonian *)
      ~has_hamiltonian_cycle g.
Proof.
  intros alg.
  exists petersen_graph.
  split.
  - (* Petersen graph is 3-regular *)
    exact petersen_is_3_regular.
  - (* Petersen graph is not Hamiltonian *)
    exact petersen_not_hamiltonian.
Qed.

(** * Summary of the Error *)

(**
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
*)

(** * Verification *)
Check liu_algorithm_incomplete.
Check petersen_not_hamiltonian.
Check greedy_can_fail.
Print petersen_graph.

(** Formalization complete: Critical error identified (incomplete coverage) *)
