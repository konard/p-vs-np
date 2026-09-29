(*
  Basic.thy - Simple foundational proofs in Isabelle/HOL

  This file serves as a bootstrap for formal verification in Isabelle,
  demonstrating basic proof techniques and serving as a template for
  future P vs NP related proofs.
*)

theory Basic
  imports Main
begin

section \<open>Basic Logical Proofs\<close>

theorem modus_ponens:
  assumes "P" and "P \<longrightarrow> Q"
  shows "Q"
  using assms by simp

theorem and_commutative:
  shows "P \<and> Q \<longrightarrow> Q \<and> P"
  by auto

theorem or_commutative:
  shows "P \<or> Q \<longrightarrow> Q \<or> P"
  by auto

section \<open>Basic Arithmetic Proofs\<close>

theorem add_zero_right:
  shows "n + 0 = (n :: nat)"
  by simp

theorem zero_add_left:
  shows "0 + n = (n :: nat)"
  by simp

theorem add_commutative:
  shows "m + n = n + (m :: nat)"
  by simp

theorem mul_one_right:
  shows "n * 1 = (n :: nat)"
  by simp

theorem one_mul_left:
  shows "1 * n = (n :: nat)"
  by simp

theorem add_associative:
  shows "(a + b) + c = a + (b + c :: nat)"
  by simp

section \<open>Even Numbers\<close>

definition is_even :: "nat \<Rightarrow> bool" where
  "is_even n \<equiv> \<exists>k. n = 2 * k"

theorem double_is_even:
  shows "is_even (2 * n)"
  unfolding is_even_def by auto

section \<open>Factorial Function\<close>

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1" |
  "factorial (Suc n) = Suc n * factorial n"

theorem factorial_positive:
  shows "0 < factorial n"
  by (induction n) auto

section \<open>List Operations\<close>

theorem list_length_append:
  shows "length (xs @ ys) = length xs + length (ys :: 'a list)"
  by simp

section \<open>Identity and Reflexivity\<close>

theorem reflexivity:
  shows "x = x"
  by simp

section \<open>Verification Summary\<close>

text \<open>
  All basic Isabelle/HOL proofs have been verified successfully.
  These foundational proofs demonstrate:
  - Propositional logic
  - Natural number arithmetic
  - Function definitions and properties
  - List operations
  - Basic proof techniques (auto, simp, induction)
\<close>

end
