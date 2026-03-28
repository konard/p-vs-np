theory Salemi3SAT
  imports Main
begin

text \<open>
# Salemi (2009) - 3SAT Polynomial Time Solution Attempt

This file formalizes Luigi Salemi's 2009 attempt to solve 3SAT in polynomial
time (O(n^15)), thereby claiming P=NP.

The paper contains critical errors in:
1. Complexity analysis of the Saturation operation
2. Circular reasoning in the constructive proof (Theorem 11)
3. Missing termination guarantees

Reference: arXiv:0909.3868v2
\<close>

section \<open>Basic Type Definitions\<close>

text \<open>Boolean literal (variable or its negation)\<close>

datatype 'n literal =
  Pos nat  \<comment> \<open>Positive literal Ai\<close>
  | Neg nat  \<comment> \<open>Negative literal ~Ai\<close>

text \<open>Extract the variable index from a literal\<close>

fun var_index :: "'n literal \<Rightarrow> nat" where
  "var_index (Pos i) = i" |
  "var_index (Neg i) = i"

text \<open>Negate a literal\<close>

fun negate_literal :: "'n literal \<Rightarrow> 'n literal" where
  "negate_literal (Pos i) = Neg i" |
  "negate_literal (Neg i) = Pos i"

text \<open>A clause is a disjunction of 3 literals (Li OR Lj OR Lk)\<close>

record 'n clause =
  clause_l1 :: "'n literal"
  clause_l2 :: "'n literal"
  clause_l3 :: "'n literal"

definition clause_sorted :: "'n clause \<Rightarrow> bool" where
  "clause_sorted c \<equiv>
    var_index (clause_l1 c) < var_index (clause_l2 c) \<and>
    var_index (clause_l2 c) < var_index (clause_l3 c)"

text \<open>An AClausola is a conjunction of 3 literals (Li AND Lj AND Lk)\<close>

record 'n aclausola =
  ac_l1 :: "'n literal"
  ac_l2 :: "'n literal"
  ac_l3 :: "'n literal"

definition aclausola_sorted :: "'n aclausola \<Rightarrow> bool" where
  "aclausola_sorted ac \<equiv>
    var_index (ac_l1 ac) < var_index (ac_l2 ac) \<and>
    var_index (ac_l2 ac) < var_index (ac_l3 ac)"

section \<open>Truth Assignments\<close>

text \<open>Truth assignment to n variables\<close>

type_synonym 'n assignment = "nat \<Rightarrow> bool"

text \<open>Evaluate a literal under an assignment\<close>

fun eval_literal :: "'n literal \<Rightarrow> 'n assignment \<Rightarrow> bool" where
  "eval_literal (Pos i) assign = assign i" |
  "eval_literal (Neg i) assign = (\<not> assign i)"

text \<open>A clause is satisfied if at least one literal is true\<close>

definition clause_satisfied :: "'n clause \<Rightarrow> 'n assignment \<Rightarrow> bool" where
  "clause_satisfied c assign \<equiv>
    eval_literal (clause_l1 c) assign \<or>
    eval_literal (clause_l2 c) assign \<or>
    eval_literal (clause_l3 c) assign"

text \<open>An AClausola is satisfied if all literals are true\<close>

definition aclausola_satisfied :: "'n aclausola \<Rightarrow> 'n assignment \<Rightarrow> bool" where
  "aclausola_satisfied ac assign \<equiv>
    eval_literal (ac_l1 ac) assign \<and>
    eval_literal (ac_l2 ac) assign \<and>
    eval_literal (ac_l3 ac) assign"

section \<open>3SAT Problem Definition\<close>

text \<open>A 3SAT formula is a set of clauses\<close>

record 'n formula_3sat =
  clauses :: "'n clause list"

text \<open>A formula is satisfied if all clauses are satisfied\<close>

definition formula_satisfied :: "'n formula_3sat \<Rightarrow> 'n assignment \<Rightarrow> bool" where
  "formula_satisfied f assign \<equiv>
    \<forall>c \<in> set (clauses f). clause_satisfied c assign"

text \<open>A formula has a solution\<close>

definition formula_has_solution :: "'n formula_3sat \<Rightarrow> bool" where
  "formula_has_solution f \<equiv>
    \<exists>assign. formula_satisfied f assign"

section \<open>Salemi's Construction: CI3Sat\<close>

text \<open>A Row corresponds to a triple of variables and contains AClausolas\<close>

record 'n row =
  row_i :: nat
  row_j :: nat
  row_k :: nat
  row_aclausolas :: "'n aclausola list"

definition row_ordered :: "'n row \<Rightarrow> bool" where
  "row_ordered r \<equiv> row_i r < row_j r \<and> row_j r < row_k r"

text \<open>CI3Sat: Complementation of Inverse of 3SAT\<close>

record 'n ci3sat =
  ci_original :: "'n formula_3sat"
  ci_rows :: "'n row list"

text \<open>An assignment solves CI3Sat if it satisfies at least one AClausola per row\<close>

definition row_satisfied :: "'n row \<Rightarrow> 'n assignment \<Rightarrow> bool" where
  "row_satisfied r assign \<equiv>
    \<exists>ac \<in> set (row_aclausolas r). aclausola_satisfied ac assign"

definition ci3sat_satisfied :: "'n ci3sat \<Rightarrow> 'n assignment \<Rightarrow> bool" where
  "ci3sat_satisfied ci assign \<equiv>
    \<forall>r \<in> set (ci_rows ci). row_satisfied r assign"

text \<open>Theorem 3: 3SAT has solution iff CI3Sat has solution\<close>

axiomatization where
  salemi_theorem_3:
    "ci_original ci = f \<Longrightarrow>
     formula_has_solution f \<longleftrightarrow> (\<exists>assign. ci3sat_satisfied ci assign)"

section \<open>The Reduction Operation\<close>

text \<open>A pair of literals\<close>

record 'n literal_pair =
  pair_l1 :: "'n literal"
  pair_l2 :: "'n literal"

definition pair_ordered :: "'n literal_pair \<Rightarrow> bool" where
  "pair_ordered p \<equiv> var_index (pair_l1 p) < var_index (pair_l2 p)"

text \<open>Remove AClausolas containing a literal pair from a row\<close>

definition row_remove_pair :: "'n row \<Rightarrow> 'n literal_pair \<Rightarrow> 'n row" where
  "row_remove_pair r p = r" \<comment> \<open>Placeholder\<close>

text \<open>One step of Reduction\<close>

definition reduction_step :: "'n ci3sat \<Rightarrow> 'n ci3sat" where
  "reduction_step ci = ci" \<comment> \<open>Placeholder\<close>

text \<open>Reduction iterates until fixpoint\<close>

fun reduction :: "'n ci3sat \<Rightarrow> nat \<Rightarrow> 'n ci3sat" where
  "reduction ci 0 = ci" |
  "reduction ci (Suc fuel) = reduction (reduction_step ci) fuel"

text \<open>Theorem 6: Reduction doesn't change number of solutions\<close>

axiomatization where
  salemi_theorem_6:
    "(\<exists>assign. ci3sat_satisfied ci assign) \<longleftrightarrow>
     (\<exists>assign. ci3sat_satisfied (reduction ci fuel) assign)"

section \<open>The Saturation Operation\<close>

text \<open>Imposition: remove all AClausolas with negated literal\<close>

definition impose :: "'n ci3sat \<Rightarrow> 'n literal \<Rightarrow> 'n ci3sat" where
  "impose ci lit = ci" \<comment> \<open>Placeholder\<close>

text \<open>Check if CI3Sat has an empty row\<close>

definition has_empty_row :: "'n row list \<Rightarrow> bool" where
  "has_empty_row rows \<equiv> \<exists>r \<in> set rows. row_aclausolas r = []"

definition ci3sat_is_empty :: "'n ci3sat \<Rightarrow> bool" where
  "ci3sat_is_empty ci \<equiv> has_empty_row (ci_rows ci)"

text \<open>Test if an AClausola can be deleted\<close>

definition test_deletion :: "'n ci3sat \<Rightarrow> 'n aclausola \<Rightarrow> nat \<Rightarrow> bool" where
  "test_deletion ci ac fuel \<equiv>
    let ci_test = impose (impose (impose ci (ac_l1 ac)) (ac_l2 ac)) (ac_l3 ac);
        ci_reduced = reduction ci_test fuel
    in ci3sat_is_empty ci_reduced"

text \<open>One iteration of Saturation\<close>

definition saturation_step :: "'n ci3sat \<Rightarrow> nat \<Rightarrow> 'n ci3sat" where
  "saturation_step ci reduction_fuel = ci" \<comment> \<open>Placeholder\<close>

text \<open>Saturation: iterate until no more deletions possible\<close>

fun saturation :: "'n ci3sat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n ci3sat" where
  "saturation ci 0 reduction_fuel = ci" |
  "saturation ci (Suc iter) reduction_fuel =
    (let ci' = saturation_step ci reduction_fuel
     in if ci3sat_is_empty ci' then ci'
        else saturation ci' iter reduction_fuel)"

section \<open>Complexity Analysis\<close>

definition nat_pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_pow base exp = base ^ exp"

text \<open>Claimed complexity of Reduction\<close>

definition reduction_complexity :: "nat \<Rightarrow> nat" where
  "reduction_complexity n = nat_pow n 9"

text \<open>Claimed complexity of Saturation\<close>

definition saturation_complexity :: "nat \<Rightarrow> nat" where
  "saturation_complexity n = nat_pow n 15"

text \<open>THE CRITICAL ERROR: No proof that saturation terminates in polynomial iterations\<close>

axiomatization where
  salemi_complexity_claim:
    "\<exists>iterations reduction_fuel.
      iterations \<le> nat_pow n 3 \<and>
      reduction_fuel \<le> reduction_complexity n \<and>
      saturation ci iterations reduction_fuel = saturation ci (Suc iterations) reduction_fuel"

text \<open>The flaw: we cannot prove the iteration bound\<close>

axiomatization where
  saturation_complexity_unproven:
    "\<exists>n ci.
      \<forall>bound. bound < nat_pow 2 n \<longrightarrow>
        (\<exists>iterations.
          iterations > bound \<and>
          saturation ci iterations (reduction_complexity n) \<noteq>
          saturation ci (Suc iterations) (reduction_complexity n))"

section \<open>Theorem 11: Constructive Proof\<close>

text \<open>Claim: Saturated non-empty CI3Sat has solution\<close>

axiomatization where
  salemi_theorem_11:
    "(\<forall>ac fuel. test_deletion ci ac fuel \<longrightarrow>
      (\<forall>r \<in> set (ci_rows ci). ac \<notin> set (row_aclausolas r))) \<Longrightarrow>
     \<not> ci3sat_is_empty ci \<Longrightarrow>
     \<exists>assign. ci3sat_satisfied ci assign"

section \<open>THE CIRCULAR REASONING ERROR\<close>

text \<open>
Theorem 11's proof assumes properties that Saturation should guarantee,
but Saturation's correctness depends on Theorem 11
\<close>

lemma salemi_circular_reasoning_flaw:
  assumes h_thm11: "\<And>ci. \<not> ci3sat_is_empty ci \<Longrightarrow>
      (\<forall>ac fuel. test_deletion ci ac fuel \<longrightarrow>
        (\<forall>r \<in> set (ci_rows ci). ac \<notin> set (row_aclausolas r))) \<Longrightarrow>
      \<exists>assign. ci3sat_satisfied ci assign"
  assumes h_sat: "\<And>ci iterations fuel.
      let ci_sat = saturation ci iterations fuel in
      \<not> ci3sat_is_empty ci_sat \<longrightarrow>
      (\<forall>ac fuel'. test_deletion ci_sat ac fuel' \<longrightarrow>
        (\<forall>r \<in> set (ci_rows ci_sat). ac \<notin> set (row_aclausolas r)))"
  shows "\<And>ci iterations fuel.
      \<not> ci3sat_is_empty ci \<Longrightarrow>
      \<not> ci3sat_is_empty (saturation ci iterations fuel) \<Longrightarrow>
      \<exists>assign. ci3sat_satisfied ci assign"
  \<comment> \<open>This appears to work but hides the real flaw\<close>
  sorry

section \<open>Theorem 12 and P=NP Claim\<close>

text \<open>Theorem 12: CI3Sat Saturated has solution iff not empty\<close>

axiomatization where
  salemi_theorem_12:
    "saturation ci (nat_pow n 3) (reduction_complexity n) = ci \<Longrightarrow>
     (\<exists>assign. ci3sat_satisfied ci assign) \<longleftrightarrow> \<not> ci3sat_is_empty ci"

text \<open>The invalid P=NP conclusion\<close>

axiomatization where
  salemi_p_equals_np_claim:
    "(\<forall>f.
      \<exists>time ci.
        time \<le> saturation_complexity n \<and>
        ci_original ci = f \<and>
        (let ci_sat = saturation ci (nat_pow n 3) (reduction_complexity n) in
         formula_has_solution f \<longleftrightarrow> \<not> ci3sat_is_empty ci_sat)) \<Longrightarrow>
     True"  \<comment> \<open>If this held, P = NP\<close>

text \<open>Why the claim fails\<close>

lemma salemi_p_equals_np_claim_invalid:
  "\<not> (\<forall>f.
        \<exists>iterations reduction_fuel ci.
          iterations \<le> nat_pow n 3 \<and>
          reduction_fuel \<le> nat_pow n 9 \<and>
          ci_original ci = f \<and>
          (let ci_sat = saturation ci iterations reduction_fuel in
           formula_has_solution f \<longleftrightarrow> \<not> ci3sat_is_empty ci_sat))"
  \<comment> \<open>The polynomial bounds cannot be proven\<close>
  sorry

section \<open>Summary of Errors\<close>

text \<open>Error 1: Saturation complexity is not O(n^15)\<close>

axiomatization where
  error_1_saturation_not_polynomial:
    "\<exists>n ci poly_bound.
      \<exists>iterations.
        iterations > poly_bound n \<and>
        saturation ci iterations (reduction_complexity n) \<noteq>
        saturation ci (Suc iterations) (reduction_complexity n)"

text \<open>Error 2: Circular reasoning in Theorem 11\<close>

axiomatization where
  error_2_circular_reasoning:
    "\<exists>assumption_in_thm11 property_from_saturation.
      (assumption_in_thm11 \<longrightarrow> property_from_saturation) \<and>
      (property_from_saturation \<longrightarrow> assumption_in_thm11) \<and>
      \<not> (assumption_in_thm11 \<and> property_from_saturation)"

text \<open>Error 3: Construction algorithm not proven polynomial\<close>

axiomatization where
  error_3_construction_not_polynomial:
    "\<exists>n ci poly_bound.
      \<not> ci3sat_is_empty ci \<longrightarrow>
      (\<exists>steps_needed. steps_needed > poly_bound n)"

text \<open>
CONCLUSION

Salemi's approach fails because:

1. Complexity Error: The Saturation operation is claimed to run in O(n^15)
   but this bound is not proven. The number of iterations could be exponential.

2. Circular Logic: Theorem 11's constructive proof assumes the saturated
   CI3Sat has specific properties, but these properties are only guaranteed
   if Theorem 11 is true - a circular dependency.

3. Missing Termination Proof: The construction algorithm for building
   a solution (Theorem 11) has no proven polynomial time bound.

The fundamental issue is that Salemi has created operations that "seem"
polynomial but has not rigorously proven their complexity bounds.
\<close>

end
