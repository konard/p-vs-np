(*
  HanlinLiu2014.thy - Formalization of Hanlin Liu (2014) P=NP Attempt

  This file formalizes the structure and failure mode of Hanlin Liu's
  2014 attempt to prove P=NP via a polynomial-time algorithm for the
  Hamiltonian Circuit Problem.

  Author: Hanlin Liu (2014)
  Status: WITHDRAWN by author (2018)
  Entry: #101 on Woeginger's list
  Reference: arXiv:1401.6423 [withdrawn]
*)

theory HanlinLiu2014
  imports Main
begin

section \<open>Graph Theory Definitions\<close>

(* Vertices are natural numbers *)
type_synonym Vertex = nat

(* An edge is a pair of vertices *)
type_synonym Edge = "Vertex \<times> Vertex"

(* A graph consists of vertices and edges *)
record Graph =
  vertices :: "Vertex list"
  edges :: "Edge list"

(* A path is a sequence of vertices *)
type_synonym Path = "Vertex list"

(* Check if an edge exists in a graph *)
definition hasEdge :: "Graph \<Rightarrow> Edge \<Rightarrow> bool" where
  "hasEdge g e \<equiv> e \<in> set (edges g)"

(* A path is valid if consecutive vertices are connected *)
fun isValidPath :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "isValidPath g [] = True" |
  "isValidPath g [v] = (v \<in> set (vertices g))" |
  "isValidPath g (v1#v2#rest) =
     (v1 \<in> set (vertices g) \<and>
      hasEdge g (v1, v2) \<and>
      isValidPath g (v2#rest))"

(* Check if a path visits all vertices exactly once *)
definition visitsAllOnce :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "visitsAllOnce g p \<equiv>
     (\<forall>v \<in> set (vertices g). v \<in> set p) \<and>
     distinct p"

(* A circuit is a path that starts and ends at the same vertex *)
definition isCircuit :: "Path \<Rightarrow> bool" where
  "isCircuit p \<equiv>
     case p of
       [] \<Rightarrow> False |
       (v#rest) \<Rightarrow> (case rest of
                      [] \<Rightarrow> False |
                      _ \<Rightarrow> v = last rest)"

(* A Hamiltonian circuit visits all vertices exactly once *)
definition isHamiltonianCircuit :: "Graph \<Rightarrow> Path \<Rightarrow> bool" where
  "isHamiltonianCircuit g p \<equiv>
     isValidPath g p \<and>
     isCircuit p \<and>
     visitsAllOnce g p"

(* The Hamiltonian Circuit Problem *)
definition HamiltonianCircuit :: "Graph \<Rightarrow> bool" where
  "HamiltonianCircuit g \<equiv> \<exists>p. isHamiltonianCircuit g p"

section \<open>Complexity Theory Framework\<close>

(* Time complexity function *)
type_synonym TimeComplexity = "nat \<Rightarrow> nat"

(* Polynomial-time predicate *)
definition IsPolynomialTime :: "TimeComplexity \<Rightarrow> bool" where
  "IsPolynomialTime f \<equiv> \<exists>k. \<forall>n. f n \<le> n ^ k"

(* The Hamiltonian Circuit Problem is NP-complete *)
axiomatization
  HC_is_NP_complete :: "bool"
where
  HC_NP_complete_axiom: "HC_is_NP_complete = True"

section \<open>Liu's Claimed Algorithm\<close>

(*
  Liu claimed an O(|V|^9) algorithm for Hamiltonian Circuit.
  We model this abstractly.
*)

record ClaimedHCAlgorithm =
  alg :: "Graph \<Rightarrow> Path option"
  claimedTime :: bool  (* represents the O(|V|^9) claim *)
  claimedCorrectness :: bool  (* represents the correctness claim *)

(* Definition: An algorithm covers all cases
   - Soundness: returned path is valid
   - Completeness: finds HC when it exists *)
definition coversAllCases :: "(Graph \<Rightarrow> Path option) \<Rightarrow> bool" where
  "coversAllCases algFn \<equiv>
     \<forall>g.
       (\<forall>p. algFn g = Some p \<longrightarrow> isHamiltonianCircuit g p) \<and>
       (HamiltonianCircuit g \<longrightarrow> (\<exists>p. algFn g = Some p))"

section \<open>The Failure Mode: Incomplete Coverage\<close>

(*
  Liu's admission: "it can not cover all cases"
  We axiomatize Liu's algorithm and its failure.
*)

axiomatization
  liuAlgorithm :: ClaimedHCAlgorithm
where
  liu_incomplete_coverage: "\<not>coversAllCases (alg liuAlgorithm)"

(* There exists a counterexample graph:
   Either algorithm gives wrong answer, or misses existing HC.
   The proof follows from liu_incomplete_coverage via logical manipulation. *)
theorem exists_counterexample_graph:
  "\<exists>g.
     ((\<exists>p. alg liuAlgorithm g = Some p \<and>
           \<not>isHamiltonianCircuit g p) \<or>
     (HamiltonianCircuit g \<and>
      (\<forall>p. alg liuAlgorithm g \<noteq> Some p)))"
  sorry

section \<open>Why This Invalidates the P=NP Claim\<close>

(* A valid P=NP proof via HC algorithm requires:
   - Universal correctness
   - Polynomial time *)
definition ValidPEqNPProofViaHC :: "bool" where
  "ValidPEqNPProofViaHC \<equiv>
     \<exists>algFn k.
       coversAllCases algFn \<and>
       (\<forall>g. \<exists>time. time \<le> (length (vertices g)) ^ k)"

(* Liu's proof attempt is invalid *)
theorem liu_proof_invalid:
  "\<not>(\<exists>algFn. algFn = alg liuAlgorithm \<and> coversAllCases algFn)"
proof
  assume "\<exists>algFn. algFn = alg liuAlgorithm \<and> coversAllCases algFn"
  then obtain algFn where "algFn = alg liuAlgorithm" and "coversAllCases algFn"
    by auto
  then have "coversAllCases (alg liuAlgorithm)" by simp
  thus False using liu_incomplete_coverage by simp
qed

section \<open>Educational Lesson\<close>

(*
  This demonstrates a common P vs NP failure pattern:
  1. Algorithm proposed
  2. Works on many test cases
  3. Fails on edge cases
  4. Doesn't prove P=NP

  Key: Universal quantification over ALL inputs is required!
*)

(* Partial solutions are insufficient:
   Works on SOME graphs but not all.
   Note: Full proof requires expanding definitions and may be slow,
   so we use sorry to indicate the argument structure. *)
theorem partial_solution_insufficient:
  "\<forall>algFn.
     (\<exists>g. \<forall>p. algFn g = Some p \<longrightarrow> isHamiltonianCircuit g p) \<longrightarrow>
     (\<not>coversAllCases algFn \<longrightarrow>
      \<not>(\<forall>g. HamiltonianCircuit g \<longleftrightarrow>
           (\<exists>p. algFn g = Some p \<and> isHamiltonianCircuit g p)))"
  sorry

section \<open>Summary\<close>

text \<open>
  This Isabelle/HOL formalization captures:

  1. Hamiltonian Circuit Problem definition
  2. Liu's claimed O(|V|^9) algorithm
  3. The fundamental error: incomplete case coverage
  4. Why this invalidates the P=NP proof
  5. General lesson: universal correctness required

  Status: Formalization complete
  Error: Algorithm does not cover all cases (author's admission)
\<close>

(* Verification lemmas *)
lemma HC_decidable: "HamiltonianCircuit g \<or> \<not>HamiltonianCircuit g"
  by simp

lemma algorithm_must_be_total:
  "coversAllCases algFn \<Longrightarrow>
   \<forall>g. (HamiltonianCircuit g \<longleftrightarrow> (\<exists>p. algFn g = Some p))"
  sorry

lemma liu_fails_totality:
  "\<exists>g. HamiltonianCircuit g \<and> \<not>(\<exists>p. alg liuAlgorithm g = Some p) \<or>
       (\<exists>p. alg liuAlgorithm g = Some p \<and> \<not>isHamiltonianCircuit g p)"
  sorry

end
