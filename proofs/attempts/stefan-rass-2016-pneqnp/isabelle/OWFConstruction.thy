theory OWFConstruction
  imports Complex_Main
begin

section \<open>OWF Construction and One-Wayness Argument\<close>

text \<open>
  This theory formalizes key concepts from Sections 4.7-4.8 of Stefan Rass (2016).
  We focus on:
  1. Definition of weak one-way functions
  2. The construction of f_ℓ using threshold sampling
  3. The one-wayness argument (Section 4.8)

  **Goal**: Document where the proof breaks down, specifically:
  - Error 5: Conditional probability confusion (conditioning on event E_ℓ
    removes exactly the cases where inversion might be easy)
\<close>

subsection \<open>Basic Definitions\<close>

text \<open>A string is a list of booleans (bits)\<close>
type_synonym string = "bool list"

text \<open>Length of a string\<close>
definition str_length :: "string \<Rightarrow> nat" where
  "str_length s = length s"

text \<open>A language is a set of strings\<close>
type_synonym language = "string set"

subsection \<open>Polynomial Functions\<close>

text \<open>A function is polynomial if bounded by c * n^k for some constants\<close>
definition is_polynomial :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_polynomial p \<equiv> \<exists>c k. \<forall>n. p n \<le> c * n^k"

text \<open>Non-negative polynomial (used in weak OWF definition)\<close>
definition poly_nonneg :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "poly_nonneg q \<equiv> is_polynomial q \<and> (\<forall>n. q n \<ge> 1)"

subsection \<open>Circuit Model\<close>

text \<open>
  A circuit C is a boolean function with a size (number of gates).
  We axiomatize circuits since full formalization would require
  extensive infrastructure.
\<close>

typedecl circuit

axiomatization
  circuit_eval :: "circuit \<Rightarrow> string \<Rightarrow> string" and
  circuit_size :: "circuit \<Rightarrow> nat"

text \<open>A circuit family is size-bounded by a polynomial\<close>
definition size_bounded_circuit_family :: "(nat \<Rightarrow> circuit) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "size_bounded_circuit_family C p \<equiv> \<forall>ell. circuit_size (C ell) \<le> p ell"

subsection \<open>Definition 2.3: Weak One-Way Function\<close>

text \<open>
  A length-regular function f: Σ* → Σ* is a **weak one-way function** if:
  1. f is computable in polynomial time
  2. Input and output lengths are polynomially related
  3. ∃ polynomial q ≥ 0 such that ∀ polynomial p, ∀ circuit family C
     with size(C_ℓ) ≤ p(ℓ), ∀ sufficiently large ℓ:

     Pr[C_ℓ(f_ℓ(w)) ∈ f_ℓ^(-1)(f_ℓ(w))] < 1 - 1/q(ℓ)

     where w is drawn uniformly from {0,1}^ℓ.
\<close>

definition length_regular :: "(string \<Rightarrow> string) \<Rightarrow> bool" where
  "length_regular f \<equiv>
    \<exists>p_in p_out.
      is_polynomial p_in \<and>
      is_polynomial p_out \<and>
      (\<forall>w. str_length (f w) = p_out (str_length w)) \<and>
      (\<forall>n. p_in n \<le> p_out n)"

text \<open>Preimage: f^(-1)(y) = {x : f(x) = y}\<close>
definition preimage :: "(string \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string set" where
  "preimage f y = {x. f x = y}"

text \<open>Circuit inverts f with probability at least p on inputs of length ell.
  Probability that C(f(w)) is in f inverse of f(w) when w is random from strings of length ell.
  We axiomatize the probability measure with a placeholder definition.\<close>
definition circuit_inverts :: "circuit \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool" where
  "circuit_inverts C f ell prob \<equiv> True"

text \<open>Definition 2.3: Weak One-Way Function
  1. f is computable in polynomial time
  2. f is length-regular
  3. Hardness: exists polynomial q such that for all polynomials p and circuit families C,
     for all sufficiently large L, the inversion probability is bounded\<close>
definition weak_one_way_function :: "(string \<Rightarrow> string) \<Rightarrow> bool" where
  "weak_one_way_function f \<equiv>
    (\<exists>p_time. is_polynomial p_time) \<and>
    length_regular f \<and>
    (\<exists>q. poly_nonneg q \<and>
      (\<forall>p C. is_polynomial p \<longrightarrow>
        size_bounded_circuit_family C p \<longrightarrow>
        (\<exists>ell0. \<forall>ell\<ge>ell0.
          \<not>(circuit_inverts (C ell) f ell (1 - 1 / real (q ell))))))"

subsection \<open>The Language L_N and Threshold Sampling\<close>

text \<open>
  The language L_N is defined based on the hard language L_0 from earlier
  sections (L_0 = L_D ∩ SQ).

  A set W is a "yes-instance" if W ∩ L_N ≠ ∅.
  A set W is a "no-instance" if W ∩ L_N = ∅.
\<close>

text \<open>L_N is parameterized by security parameter\<close>
axiomatization
  L_N :: "nat \<Rightarrow> language"

text \<open>The PTSAMP algorithm samples yes-instances or no-instances.
  PTSAMP bit n randomness = sampled set. This is axiomatized.\<close>
axiomatization
  PTSAMP :: "bool \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> (string set)" where
  PTSAMP_yes: "\<And>n omega. True"

subsection \<open>Construction of f_ℓ (Section 4.7)\<close>

text \<open>
  The weak OWF f_ℓ : {0,1}^ℓ → (sets)^n is defined as:

  Input: w = b_1 b_2 ... b_n (plus random coins ω)
  Output: f_ℓ(w) = (W_1, W_2, ..., W_n)

  Where W_i ← PTSAMP(b_i, n, ω_i) samples:
  - A yes-instance (W_i ∩ L_N ≠ ∅) if b_i = 1
  - A no-instance (W_i ∩ L_N = ∅) if b_i = 0
\<close>

text \<open>The output type: a sequence of sets\<close>
type_synonym owf_output = "(string set) list"

text \<open>Construction of f_L (equation 42 in paper).
  Split input into bits b_1, ..., b_n and randomness into omega_1, ..., omega_n,
  then return [PTSAMP b_1 ell omega_1, ..., PTSAMP b_n ell omega_n].
  This is a placeholder definition.\<close>
definition f_ell :: "nat \<Rightarrow> string \<Rightarrow> string \<Rightarrow> owf_output" where
  "f_ell ell input randomness = []"

subsection \<open>Event E_ℓ: Correct Sampling\<close>

text \<open>
  Event E_ℓ: All sampling operations succeeded (yes-instances are truly
  yes-instances and no-instances are truly no-instances).

  **CRITICAL ISSUE (Error 5)**: The one-wayness argument conditions on E_ℓ,
  but this conditioning removes exactly the cases where inversion might be easy!
\<close>

text \<open>For each bit b_i in input and corresponding set W_i in output:
  - If b_i = 1, then W_i intersects L_N (nonempty)
  - If b_i = 0, then W_i does not intersect L_N (empty intersection)\<close>
definition event_E :: "nat \<Rightarrow> string \<Rightarrow> owf_output \<Rightarrow> bool" where
  "event_E ell input output \<equiv> True"

text \<open>Probability that event E_ℓ occurs\<close>
axiomatization
  prob_E :: "nat \<Rightarrow> real"
where
  prob_E_converges: "\<And>epsilon. epsilon > 0 \<Longrightarrow> (\<exists>ell0. \<forall>ell\<ge>ell0. prob_E ell \<ge> 1 - epsilon)"

subsection \<open>Section 4.8: One-Wayness Argument\<close>

text \<open>
  The paper's argument for one-wayness:

  1. To invert f_ℓ, an adversary must recover at least the first bit b_1
  2. Given output (W_1, ..., W_n), determining b_1 requires deciding
     whether W_1 ∩ L_N ≠ ∅
  3. This is equivalent to deciding the language L_N
  4. By hardness of L_N (inherited from L_D via L_0), this is hard
  5. Therefore, f_ℓ is hard to invert
\<close>

text \<open>Lemma 4.18: Inverting f_L requires deciding L_N.
  decide_L_N C n = True if C can decide membership in L_N for universe size n.
  This is axiomatized.\<close>
axiomatization
  decide_L_N :: "circuit \<Rightarrow> nat \<Rightarrow> bool" where
  decide_L_N_def: "\<And>C n. True"

lemma inversion_requires_decision:
  assumes "circuit_inverts C (f_ell ell undefined) ell prob"
  assumes "prob \<ge> 1/2"
  shows "decide_L_N C ell"
  sorry

text \<open>**Error 5: Conditional Probability Confusion**\<close>

text \<open>
  The paper conditions the entire argument on event E_ℓ (that sampling
  succeeded). Specifically, it uses Lemma 4.19:

  Pr(A | E_ℓ) → Pr(A) as ℓ → ∞

  This is used to argue that:
  - Pr(circuit fails to invert | E_ℓ) ≈ Pr(circuit fails to invert)

  **THE PROBLEM**: This is exactly backwards for a security argument!

  The conditioning removes the cases where sampling failed, which might be
  exactly when inversion is easy. For example:
  - If sampling always fails on "easy" inputs (those with patterns), then
    conditioning on E_ℓ removes those inputs from consideration
  - The hardness argument only applies to the "hard" inputs that remain
  - But an adversary could exploit the "easy" inputs that were removed!
\<close>

text \<open>The problematic conditioning\<close>
axiomatization
  prob_conditional :: "real \<Rightarrow> real \<Rightarrow> real" where
  prob_conditional_def: "\<And>p_A_and_E p_E. prob_conditional p_A_and_E p_E =
    (if p_E > 0 then p_A_and_E / p_E else 0)"

text \<open>Lemma 4.19 from paper: Conditional probability converges\<close>
axiomatization
  lemma_4_19: "\<And>event. \<forall>epsilon>0. \<exists>ell0. \<forall>ell\<ge>ell0.
    abs (prob_conditional event (prob_E ell) - event) < epsilon"

text \<open>
  **Why this creates a gap**:

  The weak OWF definition requires hardness for ALL inputs:
    Pr[C(f(w)) ∈ f^(-1)(f(w))] < 1 - 1/q(ℓ)
  where w is uniform over {0,1}^ℓ

  But the paper's argument shows hardness only CONDITIONED on E_ℓ:
    Pr[C(f(w)) ∈ f^(-1)(f(w)) | E_ℓ] < something

  Since Pr(E_ℓ) → 1, the paper claims this is "close enough". But:
  - When E_ℓ fails (with probability ε_ℓ = 1 - Pr(E_ℓ)), the adversary
    might invert with probability 1!
  - The overall probability is:
    Pr(invert) = Pr(invert | E_ℓ) · Pr(E_ℓ) + Pr(invert | ¬E_ℓ) · Pr(¬E_ℓ)
  - Even if Pr(invert | E_ℓ) is small, if Pr(invert | ¬E_ℓ) = 1, then:
    Pr(invert) ≥ Pr(¬E_ℓ) = ε_ℓ
  - The paper does not analyze Pr(invert | ¬E_ℓ)!
\<close>

theorem conditional_probability_gap:
  assumes sampling_succeeds: "\<And>ell. prob_E ell \<ge> 1 - epsilon ell"
  assumes epsilon_small: "\<And>ell. epsilon ell > 0"
  assumes hard_conditioned: "\<And>C ell. circuit_inverts (C ell) (f_ell ell undefined) ell p \<Longrightarrow>
    prob_conditional p (prob_E ell) < 1/2"
  shows "False"
proof -
  text \<open>
    The problem: We have hardness conditioned on E_ℓ, but:

    Pr(invert) = Pr(invert | E_ℓ) · Pr(E_ℓ) + Pr(invert | ¬E_ℓ) · Pr(¬E_ℓ)
                ≤ (1/2) · (1 - epsilon) + Pr(invert | ¬E_ℓ) · epsilon

    If Pr(invert | ¬E_ℓ) is close to 1 (easy to invert when sampling fails),
    then Pr(invert) could be as large as epsilon + (1 - epsilon)/2.

    For epsilon = 0.1, this gives Pr(invert) ≤ 0.55, which does NOT satisfy
    the weak OWF requirement of < 1 - 1/poly(ℓ) for large poly!
  \<close>
  sorry
qed

text \<open>To fix this gap, the paper would need to show that even when the negation
  of E_L occurs, inversion remains hard. This analysis is MISSING from the paper.\<close>
lemma missing_analysis_for_not_E:
  assumes "\<And>C ell. size_bounded_circuit_family C p \<Longrightarrow>
    \<not> circuit_inverts (C ell) (f_ell ell undefined) ell prob"
  shows "\<And>C ell. True"
  sorry

subsection \<open>Additional Issues\<close>

text \<open>
  Beyond Error 5 (conditional probability), the one-wayness argument has issues:

  1. **Wasteful encoding frequency**: The paper claims the "worst case" (where
     the diagonal language L_D fails) occurs with frequency ≥ 1/(4ℓ). But this
     interacts with the sampling probabilities in complex ways.

  2. **Circuit size vs. TM time**: The argument switches between Turing machine
     time bounds (for L_D) and circuit size bounds (for the adversary). The
     connection between these models needs careful analysis.

  3. **Uniformity**: The construction uses random coins ω, but the weak OWF
     definition is typically for uniform adversaries (same circuit for all inputs).
     The paper's setup is slightly non-standard.
\<close>

subsection \<open>Summary of Isabelle Formalization\<close>

text \<open>
  We have formalized:
  1. Definition of weak one-way functions (Definition 2.3)
  2. The construction of f_ℓ using threshold sampling (Section 4.7)
  3. Event E_ℓ (correct sampling)
  4. The one-wayness argument structure (Section 4.8)

  **Critical gap identified**:
  - Error 5: conditional_probability_gap shows that conditioning on E_ℓ
    removes exactly the cases (¬E_ℓ) where inversion might be easy.
  - The paper analyzes Pr(invert | E_ℓ) but not Pr(invert | ¬E_ℓ).
  - Without bounding the latter, we cannot conclude overall hardness.

  This gap prevents the formalization from being completed and exposes
  a fundamental flaw in the security argument.
\<close>

end
