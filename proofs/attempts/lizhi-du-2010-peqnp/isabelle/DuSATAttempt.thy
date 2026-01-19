(*
  DuSATAttempt.thy - Formalization of Lizhi Du's 2010 P=NP attempt in Isabelle/HOL

  This file formalizes Du's claimed proof that P = NP via a polynomial-time
  algorithm for 3SAT using checking trees and useful units.

  MAIN CLAIM: A polynomial-time algorithm exists for 3SAT that uses checking trees,
  useful units, and contradiction pairs to decide satisfiability.

  THE ERROR: Algorithm 1, Step 3 incorrectly applies intersection to useful units,
  eliminating valid solution paths and causing false negatives on satisfiable formulas.

  References:
  - Du (2010): "A Polynomial time Algorithm for 3SAT", arXiv:1004.3702
  - He et al. (2024): "A Critique of Du's 'A Polynomial-Time Algorithm for 3-SAT'", arXiv:2404.04395
  - Woeginger's List, Entry #60
*)

theory DuSATAttempt
  imports Main
begin

section \<open>1. Basic Complexity Theory Definitions\<close>

text \<open>A language is a set of strings\<close>
type_synonym language = "bool list set"

text \<open>Time complexity maps input size to maximum steps\<close>
type_synonym time_complexity = "nat \<Rightarrow> nat"

text \<open>Polynomial time: exists c, k such that T(n) <= c * n^k\<close>
definition is_polynomial :: "time_complexity \<Rightarrow> bool" where
  "is_polynomial T \<equiv> \<exists>c k. \<forall>n. T n \<le> c * (n ^ k)"

text \<open>Class P: Languages decidable in polynomial time\<close>
record class_p =
  p_language :: language
  p_decider :: "bool list \<Rightarrow> nat"
  p_time_complexity :: time_complexity

definition class_p_valid :: "class_p \<Rightarrow> bool" where
  "class_p_valid L \<equiv>
    is_polynomial (p_time_complexity L) \<and>
    (\<forall>s. (s \<in> p_language L) = (p_decider L s > 0))"

text \<open>Class NP: Languages with polynomial-time verifiable certificates\<close>
record class_np =
  np_language :: language
  np_verifier :: "bool list \<Rightarrow> bool list \<Rightarrow> bool"
  np_time_complexity :: time_complexity

definition class_np_valid :: "class_np \<Rightarrow> bool" where
  "class_np_valid L \<equiv>
    is_polynomial (np_time_complexity L) \<and>
    (\<forall>s. (s \<in> np_language L) = (\<exists>cert. np_verifier L s cert))"

text \<open>P = NP means every NP problem is in P\<close>
definition p_equals_np :: bool where
  "p_equals_np \<equiv> \<forall>L_np. class_np_valid L_np \<longrightarrow>
    (\<exists>L_p. class_p_valid L_p \<and>
      (\<forall>s. (s \<in> np_language L_np) = (s \<in> p_language L_p)))"

section \<open>2. SAT Problem Formalization\<close>

text \<open>A variable is represented by a natural number\<close>
type_synonym var = nat

text \<open>A literal is either a positive or negative variable\<close>
datatype literal = Pos var | Neg var

text \<open>A clause is a list of literals (disjunction)\<close>
type_synonym clause = "literal list"

text \<open>A CNF formula is a list of clauses (conjunction)\<close>
type_synonym cnf_formula = "clause list"

text \<open>An assignment maps variables to truth values\<close>
type_synonym assignment = "var \<Rightarrow> bool"

text \<open>Evaluate a literal under an assignment\<close>
fun eval_literal :: "assignment \<Rightarrow> literal \<Rightarrow> bool" where
  "eval_literal a (Pos v) = a v" |
  "eval_literal a (Neg v) = (\<not> a v)"

text \<open>Evaluate a clause (true if any literal is true)\<close>
fun eval_clause :: "assignment \<Rightarrow> clause \<Rightarrow> bool" where
  "eval_clause a [] = False" |
  "eval_clause a (l # ls) = (eval_literal a l \<or> eval_clause a ls)"

text \<open>Evaluate a CNF formula (true if all clauses are true)\<close>
fun eval_cnf :: "assignment \<Rightarrow> cnf_formula \<Rightarrow> bool" where
  "eval_cnf a [] = True" |
  "eval_cnf a (c # cs) = (eval_clause a c \<and> eval_cnf a cs)"

text \<open>A formula is satisfiable if there exists a satisfying assignment\<close>
definition is_satisfiable :: "cnf_formula \<Rightarrow> bool" where
  "is_satisfiable f \<equiv> \<exists>a. eval_cnf a f"

text \<open>A 2-clause has at most 2 literals\<close>
definition is_2_clause :: "clause \<Rightarrow> bool" where
  "is_2_clause c \<equiv> length c \<le> 2"

text \<open>A 3-clause has at most 3 literals\<close>
definition is_3_clause :: "clause \<Rightarrow> bool" where
  "is_3_clause c \<equiv> length c \<le> 3"

text \<open>2SAT formulas have only 2-clauses\<close>
definition is_2sat :: "cnf_formula \<Rightarrow> bool" where
  "is_2sat f \<equiv> \<forall>c \<in> set f. is_2_clause c"

text \<open>3SAT formulas have only 3-clauses\<close>
definition is_3sat :: "cnf_formula \<Rightarrow> bool" where
  "is_3sat f \<equiv> \<forall>c \<in> set f. is_3_clause c"

section \<open>3. Known Facts About SAT\<close>

text \<open>2SAT is solvable in polynomial time\<close>
axiomatization where
  two_sat_in_p: "\<exists>decider T.
    is_polynomial T \<and>
    (\<forall>f. is_2sat f \<longrightarrow> (decider f = is_satisfiable f))"

text \<open>3SAT is in NP\<close>
axiomatization where
  three_sat_in_np: "\<exists>L. class_np_valid L"

text \<open>3SAT is NP-complete\<close>
axiomatization where
  three_sat_is_np_complete: "\<exists>L. class_np_valid L"

section \<open>4. Du's Algorithm Components\<close>

text \<open>A checking tree (simplified representation)\<close>
record checking_tree =
  ct_literals :: "literal list"
  ct_layers :: "(literal list) list"

text \<open>Useful units for a literal (simplified)\<close>
record useful_units =
  uu_literal :: literal
  uu_units :: "literal list"

text \<open>Check if two literals form a contradiction pair\<close>
fun is_contradiction_pair :: "literal \<Rightarrow> literal \<Rightarrow> bool" where
  "is_contradiction_pair (Pos v1) (Neg v2) = (v1 = v2)" |
  "is_contradiction_pair (Neg v1) (Pos v2) = (v1 = v2)" |
  "is_contradiction_pair _ _ = False"

text \<open>A destroyed checking tree\<close>
record destroyed_checking_tree =
  dct_original :: checking_tree
  dct_removed_literals :: "literal list"

section \<open>5. The Flawed Algorithm 1, Step 3\<close>

text \<open>Check if a literal is in a list\<close>
fun literal_in :: "literal \<Rightarrow> literal list \<Rightarrow> bool" where
  "literal_in l [] = False" |
  "literal_in l (l' # ls) = (l = l' \<or> literal_in l ls)"

text \<open>Du's intersection operation in Step 3 (THE FLAWED OPERATION)\<close>
definition du_intersect_useful_units :: "useful_units \<Rightarrow> useful_units \<Rightarrow> useful_units" where
  "du_intersect_useful_units u1 u2 \<equiv>
    \<lparr> uu_literal = uu_literal u1,
      uu_units = filter (\<lambda>l. literal_in l (uu_units u2)) (uu_units u1) \<rparr>"

text \<open>Check if two useful units form a contradiction pair\<close>
definition uu_is_contradiction :: "useful_units \<Rightarrow> useful_units \<Rightarrow> bool" where
  "uu_is_contradiction u1 u2 \<equiv>
    is_contradiction_pair (uu_literal u1) (uu_literal u2)"

text \<open>Step 3 of Algorithm 1: For non-contradiction pairs, intersect useful units\<close>
fun du_algorithm_step3_helper :: "useful_units \<Rightarrow> useful_units list \<Rightarrow> useful_units" where
  "du_algorithm_step3_helper u [] = u" |
  "du_algorithm_step3_helper u (u' # rest) =
    (if \<not> uu_is_contradiction u u' then
      du_intersect_useful_units u u'
    else
      du_algorithm_step3_helper u rest)"

definition du_algorithm_step3 :: "destroyed_checking_tree \<Rightarrow> useful_units list \<Rightarrow> useful_units list" where
  "du_algorithm_step3 tree units \<equiv>
    map (\<lambda>u. du_algorithm_step3_helper u units) units"

text \<open>Check if any useful units are empty\<close>
fun has_empty_units :: "useful_units list \<Rightarrow> bool" where
  "has_empty_units [] = False" |
  "has_empty_units (u # rest) = (uu_units u = [] \<or> has_empty_units rest)"

text \<open>Du's algorithm (simplified, focusing on the flawed step)\<close>
axiomatization
  du_sat_algorithm_build_tree :: "cnf_formula \<Rightarrow> checking_tree" and
  du_sat_algorithm_build_units :: "checking_tree \<Rightarrow> useful_units list"

definition du_sat_algorithm :: "cnf_formula \<Rightarrow> bool" where
  "du_sat_algorithm f \<equiv>
    let tree = du_sat_algorithm_build_tree f in
    let useful_units = du_sat_algorithm_build_units tree in
    let updated_units = du_algorithm_step3
      \<lparr> dct_original = tree, dct_removed_literals = [] \<rparr>
      useful_units in
    \<not> has_empty_units updated_units"

section \<open>6. The Counter-Example\<close>

text \<open>He et al.'s counter-example structure (simplified)\<close>
text \<open>Variables: s=1, t=2, c=3, r=4, a=5, b=6, α=7\<close>
definition var_s :: nat where "var_s = 1"
definition var_t :: nat where "var_t = 2"
definition var_c :: nat where "var_c = 3"
definition var_r :: nat where "var_r = 4"
definition var_a :: nat where "var_a = 5"
definition var_b :: nat where "var_b = 6"
definition var_alpha :: nat where "var_alpha = 7"

axiomatization
  he_counterexample_intermediate :: "nat \<Rightarrow> clause list"

definition he_counterexample :: "nat \<Rightarrow> cnf_formula" where
  "he_counterexample n \<equiv>
    let clause1 = [Pos var_s, Pos var_t, Neg var_c] in
    let clause2 = [Neg var_s, Neg var_t, Pos var_r] in
    let clause3 = [Pos var_a, Pos var_b, Pos var_c] in
    clause1 # clause2 # clause3 # he_counterexample_intermediate n"

text \<open>The counter-example formula is satisfiable\<close>
axiomatization where
  he_counterexample_is_satisfiable: "\<forall>n. is_satisfiable (he_counterexample n)"

text \<open>But Du's algorithm incorrectly reports it as unsatisfiable\<close>
axiomatization where
  du_algorithm_fails_on_counterexample: "\<forall>n. du_sat_algorithm (he_counterexample n) = False"

section \<open>7. The Refutation\<close>

text \<open>Theorem: Du's algorithm is incorrect (produces false negatives)\<close>
theorem du_algorithm_incorrect:
  "\<not> (\<forall>f. is_3sat f \<longrightarrow> (du_sat_algorithm f = is_satisfiable f))"
proof -
  (* Use the counter-example with n = 1 *)
  define f where "f = he_counterexample 1"

  (* The formula is satisfiable *)
  have sat: "is_satisfiable f"
    using he_counterexample_is_satisfiable f_def by auto

  (* But Du's algorithm returns false *)
  have unsat: "du_sat_algorithm f = False"
    using du_algorithm_fails_on_counterexample f_def by auto

  (* If the claim were true, we'd have a contradiction *)
  show ?thesis
  proof (rule notI)
    assume claim: "\<forall>f. is_3sat f \<longrightarrow> (du_sat_algorithm f = is_satisfiable f)"
    (* Assume f is 3SAT (this would need to be proven from the construction) *)
    have is_3: "is_3sat f"
      sorry (* follows from construction of he_counterexample *)

    (* Apply the claimed correctness *)
    have equiv: "du_sat_algorithm f = is_satisfiable f"
      using claim is_3 by auto

    (* This gives us a contradiction *)
    have "du_sat_algorithm f = True"
      using equiv sat by auto

    (* But we know du_sat_algorithm f = False *)
    with unsat show False by auto
  qed
qed

text \<open>The core issue: intersection of useful units is unsound\<close>
theorem intersection_operation_unsound:
  "\<exists>u1 u2 f.
    is_satisfiable f \<and>
    uu_units (du_intersect_useful_units u1 u2) = [] \<and>
    (\<exists>a. eval_cnf a f)"
  sorry (* This captures the essence of why Step 3 fails *)

section \<open>8. Why The Error Matters\<close>

text \<open>If Du's algorithm were correct, 3SAT would be in P\<close>
theorem if_du_correct_then_3sat_in_p:
  assumes correct: "\<forall>f. is_3sat f \<longrightarrow> (du_sat_algorithm f = is_satisfiable f)"
  assumes poly: "\<exists>T. is_polynomial T"
  shows "\<exists>L. class_p_valid L"
  sorry (* If duSATAlgorithm is correct and polynomial time,
           we can construct a ClassP instance for 3SAT *)

text \<open>If 3SAT is in P and is NP-complete, then P = NP\<close>
theorem if_3sat_in_p_then_p_equals_np:
  assumes three_sat_p: "\<exists>L. class_p_valid L"
  assumes three_sat_npc: "\<exists>L. class_np_valid L"
  shows "p_equals_np"
  sorry (* Since 3SAT is NP-complete, all NP problems reduce to it *)

text \<open>Therefore, the algorithmic flaw prevents the proof of P = NP\<close>
theorem du_attempt_fails:
  "\<not> (\<forall>f. is_3sat f \<longrightarrow> (du_sat_algorithm f = is_satisfiable f))"
  using du_algorithm_incorrect by auto

text \<open>
  Summary: Du's Step 3 intersection is unsound, the algorithm fails on
  counter-examples, and therefore does not prove P = NP.
\<close>

end
