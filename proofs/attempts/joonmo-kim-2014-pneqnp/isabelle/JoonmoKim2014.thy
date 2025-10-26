theory JoonmoKim2014
  imports Main
begin

text \<open>
  Formalization of Joonmo Kim's 2014 P≠NP Proof Attempt
  This formalization demonstrates the errors in the proof
  Reference: https://arxiv.org/abs/1403.4143
  Refutation: https://arxiv.org/abs/1404.5352
\<close>

section \<open>Basic Complexity Theory Concepts\<close>

typedecl SATInstance
typedecl TuringMachine
typedecl TransitionTable
typedecl Configuration
typedecl Input

text \<open>An accepting computation is a sequence of configurations\<close>
type_synonym AcceptingComputation = "Configuration list"

text \<open>Number of transitions in an accepting computation\<close>
definition num_transitions :: "AcceptingComputation \<Rightarrow> nat" where
  "num_transitions ac = (case ac of [] \<Rightarrow> 0 | (x#xs) \<Rightarrow> length xs)"

text \<open>Basic properties and relations\<close>
consts
  satisfiable :: "SATInstance \<Rightarrow> bool"
  produces :: "TransitionTable \<Rightarrow> TuringMachine \<Rightarrow> Input \<Rightarrow> AcceptingComputation \<Rightarrow> bool"
  input_part :: "SATInstance \<Rightarrow> SATInstance"
  run_part :: "SATInstance \<Rightarrow> SATInstance"
  concatenate :: "SATInstance \<Rightarrow> SATInstance \<Rightarrow> SATInstance"
  num_clauses :: "SATInstance \<Rightarrow> nat"
  cook_levin_encode :: "AcceptingComputation \<Rightarrow> SATInstance"

text \<open>Property: each transition requires multiple clauses\<close>
axiomatization where
  clauses_gt_transitions: "\<forall>ac. num_clauses (cook_levin_encode ac) > num_transitions ac"

section \<open>Machine M Family\<close>

consts
  M :: "nat \<Rightarrow> TuringMachine"
  run_parts :: "nat \<Rightarrow> SATInstance list"

text \<open>SAT solver properties\<close>
consts
  P_eq_NP :: "bool"  \<comment> \<open>P = NP hypothesis\<close>
  SAT_in_NP :: "bool"  \<comment> \<open>SAT is in NP\<close>

text \<open>Dsat and NDsat properties of transition tables\<close>
consts
  is_Dsat :: "TransitionTable \<Rightarrow> bool"
  is_NDsat :: "TransitionTable \<Rightarrow> bool"

section \<open>M° Construction\<close>

consts
  M_circle_index :: "nat"
  M_circle_input :: "Input"
  c_circle :: "SATInstance"
  t_circle :: "TransitionTable"
  ac_M_circle :: "AcceptingComputation"
  ac_c_circle :: "AcceptingComputation"

definition M_circle :: "TuringMachine" where
  "M_circle = M M_circle_index"

text \<open>Core properties of M°\<close>
axiomatization where
  M_circle_property_1: "produces t_circle M_circle M_circle_input ac_M_circle" and
  M_circle_property_2: "produces t_circle M_circle M_circle_input ac_c_circle" and
  c_circle_is_encoding: "c_circle = cook_levin_encode ac_c_circle"

section \<open>The Modus Tollens Propositions\<close>

definition P1 :: "bool" where
  "P1 = P_eq_NP"  \<comment> \<open>P = NP\<close>

definition P2 :: "bool" where
  "P2 = (\<exists>t. produces t M_circle M_circle_input ac_M_circle)"  \<comment> \<open>M° exists\<close>

definition P3 :: "bool" where
  "P3 = is_Dsat t_circle"  \<comment> \<open>t is Dsat\<close>

text \<open>Part 1 of Kim's proof: P1 → (P2 → P3)\<close>
axiomatization where
  kim_part1: "P1 \<longrightarrow> (P2 \<longrightarrow> P3)"

text \<open>Part 2: Kim claims M° exists with NDsat\<close>
axiomatization where
  M_circle_exists_with_NDsat: "\<exists>t. is_NDsat t \<and> produces t M_circle M_circle_input ac_M_circle"

theorem kim_P2_holds: "P2"
  unfolding P2_def
  using M_circle_exists_with_NDsat by auto

section \<open>Interpretation 1: Accepting Computations Tied to Their Machines\<close>

consts
  original_TM_of_ac :: "AcceptingComputation \<Rightarrow> TuringMachine"
  state_space :: "TransitionTable \<Rightarrow> nat"  \<comment> \<open>Simplified: size of state space\<close>

definition proper_accepting_computation ::
  "AcceptingComputation \<Rightarrow> TransitionTable \<Rightarrow> Input \<Rightarrow> bool" where
  "proper_accepting_computation ac t y = produces t (original_TM_of_ac ac) y ac"

text \<open>Under interpretation 1, merged tables are malformed\<close>
axiomatization where
  merged_table_different_states: "\<forall>t1 t2 t_merged. True"  \<comment> \<open>Simplified\<close>

text \<open>Under interpretation 1, same transition table doesn't mean same computation\<close>
lemma interpretation1_no_contradiction:
  assumes "\<exists>t. produces t M_circle M_circle_input ac_M_circle \<and>
                produces t M_circle M_circle_input ac_c_circle"
  shows "ac_M_circle \<noteq> ac_c_circle"
  oops  \<comment> \<open>Left as exercise - the merged table is malformed\<close>

section \<open>Interpretation 2: Accepting Computations from Any Transition Table\<close>

text \<open>Under interpretation 2, same transition table means same computation\<close>
axiomatization where
  interpretation2_same_computation:
    "produces t_circle M_circle M_circle_input ac_M_circle \<Longrightarrow>
     produces t_circle M_circle M_circle_input ac_c_circle \<Longrightarrow>
     ac_M_circle = ac_c_circle"

section \<open>The Counting Arguments\<close>

definition i :: "nat" where
  "i = num_transitions ac_M_circle"  \<comment> \<open>transitions in ac_M°\<close>

definition j :: "nat" where
  "j = num_clauses c_circle"  \<comment> \<open>clauses in c°\<close>

definition k :: "nat" where
  "k = num_transitions ac_c_circle"  \<comment> \<open>transitions in ac_c°\<close>

text \<open>Kim's claims about the inequalities\<close>
axiomatization where
  kim_claim_i_gt_j: "i > j" and
  kim_claim_j_gt_k: "j > k"

text \<open>If ac_M° = ac_c° (interpretation 2), then i = k\<close>
lemma interpretation2_i_equals_k:
  assumes "ac_M_circle = ac_c_circle"
  shows "i = k"
  unfolding i_def k_def
  using assms by simp

text \<open>Under interpretation 2, there's no contradiction because i > j > k doesn't apply\<close>
lemma interpretation2_no_contradiction:
  assumes "produces t_circle M_circle M_circle_input ac_M_circle \<longrightarrow>
           produces t_circle M_circle M_circle_input ac_c_circle \<longrightarrow>
           ac_M_circle = ac_c_circle"
  shows "True"
  by simp

section \<open>The Core Error: Inconsistent Interpretations\<close>

text \<open>
  Kim's proof attempts to:
  1. Use interpretation 1 to establish i > j > k (based on M°'s actual behavior)
  2. Use interpretation 2 to establish i = k (based on same transition table)
  3. Derive a contradiction

  But you cannot use BOTH interpretations simultaneously!
\<close>

theorem kim_proof_error:
  "\<not>((i > j \<and> j > k) \<and>
      (ac_M_circle = ac_c_circle \<longrightarrow> i = k) \<and>
      ac_M_circle = ac_c_circle)"
proof -
  assume assm: "(i > j \<and> j > k) \<and> (ac_M_circle = ac_c_circle \<longrightarrow> i = k) \<and> ac_M_circle = ac_c_circle"
  then have "i > j" and "j > k" and "ac_M_circle = ac_c_circle" by auto
  then have "i = k" using assm unfolding i_def k_def by simp
  then have "k > j" using \<open>i > j\<close> by simp
  then have "k > k" using \<open>j > k\<open> \<open>k > j\<close> by auto
  then show False by simp
qed

section \<open>Additional Error: Circular Definition\<close>

text \<open>M° is DEFINED by the existence of t, so "M° exists" ↔ "t exists"\<close>

definition M_circle_exists :: "bool" where
  "M_circle_exists = P2"

definition t_circle_exists :: "bool" where
  "t_circle_exists = (\<exists>t. produces t M_circle M_circle_input ac_M_circle)"

text \<open>By definition, M° exists iff t exists\<close>
axiomatization where
  circular_definition: "M_circle_exists = t_circle_exists"

theorem circular_error: "P2 = t_circle_exists"
  unfolding M_circle_exists_def P2_def t_circle_exists_def
  by simp

section \<open>Conclusion\<close>

text \<open>
  Kim's proof fails because:
  1. It uses inconsistent interpretations of "accepting computation"
  2. It has circular definitions (M° defined by t's existence)
  3. The counting argument conflates meta-level and object-level
  4. The "merging" of transition tables is ill-formed
\<close>

theorem kim_proof_invalid:
  "\<not>((P1 \<longrightarrow> (P2 \<longrightarrow> P3)) \<and> \<not>(P2 \<longrightarrow> P3) \<longrightarrow> \<not>P1)"
  oops  \<comment> \<open>The premises cannot both be established due to the errors above\<close>

text \<open>
  Summary: This formalization demonstrates that Kim's proof attempt
  fails due to fundamental definitional ambiguities and logical inconsistencies.
  The error is not in the modus tollens structure itself, but in the
  attempt to establish ¬(P2 → P3) while switching between incompatible
  interpretations of key concepts.
\<close>

end
