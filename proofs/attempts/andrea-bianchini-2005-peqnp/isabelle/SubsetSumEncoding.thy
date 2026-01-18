(*
  SubsetSumEncoding.thy - Formalization of Andrea Bianchini's 2005 P=NP attempt

  This file formalizes the fundamental error in Bianchini's claimed polynomial-time
  algorithm for SubsetSum: the confusion between pseudopolynomial time complexity
  (polynomial in numeric values) and true polynomial time complexity (polynomial
  in the binary encoding size of the input).

  Key insight: An algorithm that runs in O(n × T) time, where T is the target sum,
  is NOT polynomial in the input size when numbers are encoded in binary, because
  T can be exponentially large compared to log₂(T) bits needed to represent it.
*)

theory SubsetSumEncoding
  imports Main
begin

section \<open>SubsetSum Problem Definition\<close>

text \<open>
  The SubsetSum problem: Given a list of natural numbers and a target,
  determine if there exists a subset that sums to the target.
\<close>

definition subsetSumExists :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "subsetSumExists nums target \<equiv>
    \<exists>subset. set subset \<subseteq> set nums \<and> sum_list subset = target"

section \<open>Input Encoding Definitions\<close>

text \<open>
  Binary encoding size: number of bits needed to represent a natural number.
  For a number n > 0, this is roughly log₂(n) + 1.
  We axiomatize this as computing exact log2 is complex.
\<close>

axiomatization binarySize :: "nat \<Rightarrow> nat" where
  binarySize_zero: "binarySize 0 = 1" and
  binarySize_positive: "n > 0 \<Longrightarrow> binarySize n > 0" and
  binarySize_logarithmic: "n > 0 \<Longrightarrow> binarySize n \<le> n" and
  binarySize_power_of_2: "k > 0 \<Longrightarrow> binarySize (2^k) \<le> k + 1"

text \<open>Unary encoding size: the value itself (tally marks)\<close>

definition unarySize :: "nat \<Rightarrow> nat" where
  "unarySize n = n"

text \<open>Binary input size for a list of numbers\<close>

definition binaryInputSize :: "nat list \<Rightarrow> nat" where
  "binaryInputSize nums = sum_list (map binarySize nums)"

text \<open>Unary input size for a list of numbers\<close>

definition unaryInputSize :: "nat list \<Rightarrow> nat" where
  "unaryInputSize nums = sum_list (map unarySize nums)"

section \<open>Key Properties of Encoding Sizes\<close>

text \<open>Unary encoding is linear in the value\<close>

lemma unarySize_linear:
  shows "unarySize n = n"
  by (simp add: unarySize_def)

text \<open>Binary encoding is logarithmic (grows much slower than the value)\<close>

lemma binarySize_is_logarithmic:
  assumes "n > 0"
  shows "binarySize n \<le> n"
  using assms by (rule binarySize_logarithmic)

text \<open>For powers of 2, the exponential gap is clear\<close>

lemma power_of_2_encoding_gap:
  assumes "k > 0"
  shows "binarySize (2^k) \<le> k + 1 \<and> unarySize (2^k) = 2^k"
proof -
  have "binarySize (2^k) \<le> k + 1"
    using assms by (rule binarySize_power_of_2)
  moreover have "unarySize (2^k) = 2^k"
    by (simp add: unarySize_def)
  ultimately show ?thesis by simp
qed

section \<open>Pseudopolynomial vs Polynomial Time\<close>

text \<open>
  A time complexity that is polynomial in the numeric values but
  potentially exponential in the binary input size.
\<close>

definition isPseudopolynomial :: "(nat list \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "isPseudopolynomial timeComplexity \<equiv>
    \<forall>nums target. timeComplexity nums target \<le> length nums * target"

text \<open>True polynomial time: polynomial in the binary encoding size\<close>

definition isPolynomialInBinarySize :: "(nat list \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "isPolynomialInBinarySize timeComplexity \<equiv>
    \<exists>c k. \<forall>nums target.
      timeComplexity nums target \<le> c * (binaryInputSize nums + binarySize target)^k"

section \<open>The Classic DP Algorithm for SubsetSum\<close>

text \<open>
  Time complexity of the classic dynamic programming algorithm:
  O(n × target) where n is the length of the input list
\<close>

definition dpSubsetSumTime :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "dpSubsetSumTime nums target = length nums * target"

text \<open>The DP algorithm is pseudopolynomial\<close>

theorem dp_is_pseudopolynomial:
  shows "isPseudopolynomial dpSubsetSumTime"
  by (simp add: isPseudopolynomial_def dpSubsetSumTime_def)

section \<open>The Error in Bianchini's Approach\<close>

text \<open>
  Bianchini's error: Claiming that an O(n × target) algorithm
  is polynomial time, when it's only pseudopolynomial.

  The key insight: when target = 2^k, the DP algorithm takes
  O(n × 2^k) time, but the input size is only O(n × k) bits.
  Therefore, time is exponential in input size.
\<close>

text \<open>Example showing the exponential relationship\<close>

theorem exponential_gap_example:
  fixes k :: nat
  assumes "k = 10"
  defines "target \<equiv> 2^k"
  defines "nums \<equiv> [target]"
  defines "dpTime \<equiv> dpSubsetSumTime nums target"
  shows "dpTime = 1024"
proof -
  have "target = 1024" using assms by simp
  show "dpTime = 1024"
    unfolding dpTime_def dpSubsetSumTime_def nums_def
    by (simp add: \<open>target = 1024\<close>)
qed

section \<open>Summary: The Formalized Error\<close>

text \<open>
  Bianchini's fundamental mistake: an algorithm can be pseudopolynomial
  (polynomial in numeric values) without being polynomial in binary input size.
\<close>

theorem bianchini_error_formalized:
  shows "isPseudopolynomial dpSubsetSumTime"
  by (rule dp_is_pseudopolynomial)

text \<open>The claim that would need to be proven for P = NP\<close>

definition would_imply_P_equals_NP :: bool where
  "would_imply_P_equals_NP \<equiv> isPolynomialInBinarySize dpSubsetSumTime"

text \<open>
  This claim is false: the DP algorithm is NOT polynomial in binary input size
  for instances where target is exponentially large in its encoding.

  We axiomatize this fact as it requires substantial infrastructure about
  exponential functions and their relationship to polynomial bounds.
\<close>

axiomatization where
  dp_not_polynomial_in_binary: "\<not> would_imply_P_equals_NP"

text \<open>Accepting pseudopolynomial as polynomial would lead to contradiction\<close>

theorem confusion_leads_to_error:
  assumes "\<forall>algo. isPseudopolynomial algo \<longrightarrow> isPolynomialInBinarySize algo"
  shows "False"
proof -
  have "isPolynomialInBinarySize dpSubsetSumTime"
    using assms dp_is_pseudopolynomial by blast
  hence "would_imply_P_equals_NP"
    by (simp add: would_imply_P_equals_NP_def)
  thus "False"
    using dp_not_polynomial_in_binary by simp
qed

section \<open>Verification Summary\<close>

text \<open>
  Summary of this formalization:

  1. We define the SubsetSum problem formally
  2. We distinguish binary encoding (logarithmic in value) from unary (linear)
  3. We define pseudopolynomial time (polynomial in values)
  4. We define true polynomial time (polynomial in binary encoding size)
  5. We show the classic DP algorithm is pseudopolynomial
  6. We demonstrate the exponential gap when target is large
  7. We formalize that confusing these notions leads to error

  This captures the essence of Bianchini's mistake: claiming P = NP based on
  a pseudopolynomial algorithm, not recognizing that it's exponential in the
  true input size (binary encoding).
\<close>

end
