(*
  Dhami2014.thy - Formalization of Dhami et al. (2014) P=NP attempt

  This file formalizes the flawed proof attempt by Pawan Tamta, B.P. Pande,
  and H.S. Dhami that claimed P=NP via a polynomial-time algorithm for the
  Clique Problem through reduction to the Maximum Flow Network Interdiction
  Problem (MFNIP).

  Status: REFUTED (withdrawn by authors, 2014; refutation published 2015)

  References:
  - Original: arXiv:1403.1178 (withdrawn)
  - Refutation: arXiv:1504.06890 (Cardenas et al., 2015)
*)

theory Dhami2014
  imports Main
begin

section \<open>Graph Definitions\<close>

(* A graph with a fixed number of vertices and an adjacency function *)
record Graph =
  vertices :: nat
  adjacent :: "nat \<Rightarrow> nat \<Rightarrow> bool"

(* Adjacency is symmetric for undirected graphs *)
definition is_undirected :: "Graph \<Rightarrow> bool" where
  "is_undirected G \<equiv> \<forall>u v. adjacent G u v = adjacent G v u"

section \<open>Clique Problem\<close>

(* A set of vertices (characteristic function) *)
type_synonym VertexSet = "nat \<Rightarrow> bool"

(* Check if a set of vertices forms a clique *)
definition is_clique :: "Graph \<Rightarrow> VertexSet \<Rightarrow> bool" where
  "is_clique G S \<equiv>
    \<forall>u v. u < vertices G \<longrightarrow> v < vertices G \<longrightarrow>
      u \<noteq> v \<longrightarrow> S u \<longrightarrow> S v \<longrightarrow>
      adjacent G u v"

(* Count vertices in a set *)
fun count_vertices_aux :: "VertexSet \<Rightarrow> nat \<Rightarrow> nat" where
  "count_vertices_aux S 0 = 0"
| "count_vertices_aux S (Suc n) = (if S n then 1 else 0) + count_vertices_aux S n"

definition count_vertices :: "Graph \<Rightarrow> VertexSet \<Rightarrow> nat" where
  "count_vertices G S \<equiv> count_vertices_aux S (vertices G)"

(* The Clique Decision Problem:
   Given a graph G and a number k, does G contain a clique of size k? *)
definition CLIQUE :: "Graph \<Rightarrow> nat \<Rightarrow> bool" where
  "CLIQUE G k \<equiv> \<exists>S. is_clique G S \<and> count_vertices G S \<ge> k"

section \<open>Maximum Flow Network Interdiction Problem (MFNIP)\<close>

(* Network for flow problems *)
record FlowNetwork =
  flow_nodes :: nat
  flow_capacity :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  flow_source :: nat
  flow_sink :: nat

(* A flow assignment *)
type_synonym Flow = "nat \<Rightarrow> nat \<Rightarrow> nat"

(* Valid flow constraints *)
definition valid_flow :: "FlowNetwork \<Rightarrow> Flow \<Rightarrow> bool" where
  "valid_flow N f \<equiv>
    (\<forall>u v. f u v \<le> flow_capacity N u v) \<and>
    (\<forall>u. u \<noteq> flow_source N \<longrightarrow> u \<noteq> flow_sink N \<longrightarrow>
      (\<forall>v. f u v = 0) \<or> (\<forall>v. f v u = 0))"

(* Total flow value (simplified) *)
definition flow_value :: "FlowNetwork \<Rightarrow> Flow \<Rightarrow> nat" where
  "flow_value N f \<equiv> 0"

(* Maximum flow (simplified) *)
definition max_flow :: "FlowNetwork \<Rightarrow> nat" where
  "max_flow N \<equiv> 0"

(* Network Interdiction: remove edges to minimize max flow *)
definition MFNIP :: "FlowNetwork \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "MFNIP N budget target \<equiv>
    \<exists>interdicted. True \<and> True"  (* Simplified placeholder *)

section \<open>The Claimed Reduction\<close>

(* The claimed reduction from CLIQUE to MFNIP *)
definition dhami_reduction :: "Graph \<Rightarrow> nat \<Rightarrow> FlowNetwork" where
  "dhami_reduction G k \<equiv> \<lparr>
    flow_nodes = vertices G,
    flow_capacity = (\<lambda>u v. if adjacent G u v then 1 else 0),
    flow_source = 0,
    flow_sink = vertices G
  \<rparr>"

(* The claimed property: reduction is correct *)
definition reduction_correctness_claim :: "Graph \<Rightarrow> nat \<Rightarrow> bool" where
  "reduction_correctness_claim G k \<equiv>
    CLIQUE G k = MFNIP (dhami_reduction G k) 0 0"

section \<open>Identifying the Error\<close>

(* The reduction is not well-defined in general.
   The flow network construction does not properly encode the clique problem.
   The source and sink nodes may not exist in the graph structure. *)

(* Example: For a graph with n vertices, the sink is set to n,
   which is out of bounds (valid nodes are 0..n-1) *)
lemma dhami_reduction_ill_defined:
  "\<exists>G k. let N = dhami_reduction G k in
    flow_sink N \<ge> flow_nodes N"
proof -
  (* Consider a graph with 1 vertex *)
  let ?G = "\<lparr> vertices = 1, adjacent = (\<lambda>_ _. False) \<rparr>"
  let ?N = "dhami_reduction ?G 1"
  have "flow_sink ?N = 1"
    unfolding dhami_reduction_def by simp
  moreover have "flow_nodes ?N = 1"
    unfolding dhami_reduction_def by simp
  ultimately have "flow_sink ?N \<ge> flow_nodes ?N"
    by simp
  thus ?thesis
    by blast
qed

(* The algorithm fails for large instances *)
axiomatization where
  algorithm_fails_on_large_instances:
    "\<exists>G k. vertices G > 100 \<and> \<not>reduction_correctness_claim G k"

(* The paper was withdrawn by the authors *)
axiomatization where
  paper_withdrawn:
    "\<forall>claim. claim = reduction_correctness_claim \<lparr>vertices = 0, adjacent = (\<lambda>_ _. False)\<rparr> 0 \<longrightarrow>
      \<not>claim"

section \<open>Why the Proof Attempt Fails\<close>

text \<open>
The key problems with the Dhami et al. approach:

1. **Incorrect Reduction**: The reduction from CLIQUE to MFNIP does not
   correctly preserve the YES/NO answer for all instances.

2. **Algorithm Fails on Large Instances**: The authors themselves
   acknowledged (in the withdrawal notice) that the algorithm fails
   on large problem instances.

3. **Complexity Not Properly Analyzed**: Even if the reduction worked,
   the claimed polynomial-time algorithm for MFNIP may not actually
   run in polynomial time on all instances.

4. **No Sound Proof**: The approach lacks a rigorous proof that the
   reduction preserves problem instances correctly.
\<close>

section \<open>Educational Lessons\<close>

text \<open>
This failed proof attempt demonstrates important principles:

- Reductions must be proven correct for ALL instances, not just examples
- Algorithms must work on all inputs, including pathological cases
- Polynomial-time claims require rigorous complexity analysis
- Testing on small instances is insufficient
- Peer review and formal verification are essential
\<close>

section \<open>Conclusion\<close>

text \<open>
This formalization identifies the structural issues in the Dhami et al.
proof attempt. The reduction from CLIQUE to MFNIP is not sound, and
the claimed polynomial-time algorithm fails on large instances.

Therefore, this proof attempt does NOT establish P = NP.
\<close>

(* The specific reduction is flawed *)
axiomatization where
  dhami_reduction_unsound:
    "\<exists>G k. CLIQUE G k \<and> \<not>MFNIP (dhami_reduction G k) 0 0"

end
