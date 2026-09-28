/-
  WenLinProof.lean — Forward Proof Formalization
  Bangyan Wen & Yi Lin (2010) P≠NP attempt

  Paper: "THE ANSWER TO THE P/NP PROBLEM IS P≠NP!"
  Journal: Scientific Inquiry — A Journal of the IIGSS, Vol. 11, No. 2, December 2010
  Woeginger List Entry: #70

  This file formalizes the original argument as faithfully as possible.

  The paper claims to prove P ≠ NP by "formal logic reasoning and analysis,"
  arguing that the existential quantifier structure of NP is fundamentally
  different from the deterministic polynomial-time structure of P.

  We formalize:
  1. The paper's logical characterizations of P and NP
  2. The asymmetry claim (∃ over exponential domain vs. deterministic unique path)
  3. The (flawed) inference that this asymmetry proves P ≠ NP
  4. Why the inference step cannot be completed without proving P ≠ NP directly

  Note: Steps marked with `sorry` cannot be completed because they require
  proving P ≠ NP itself — the very claim the paper asserts without justification.
-/

namespace WenLinProof

/- ## Basic Definitions -/

/-- Polynomial bound: f(n) ≤ c * n^k for some constants c, k -/
def IsPolynomialBound (f : Nat → Nat) : Prop :=
  ∃ (c k : Nat), c > 0 ∧ k > 0 ∧ ∀ n, n > 0 → f n ≤ c * n ^ k

/-- A decision problem as a language (set of natural numbers encoding inputs) -/
def Language := Nat → Bool

/-- A Turing machine (deterministic) is modeled as a function from input to output -/
def DetTM := Nat → Bool

/-- Running time of a TM: modeled as a function Nat → Nat -/
def RunningTime := Nat → Nat

/-- A problem L is in P: there is a det. TM that decides it in polynomial time -/
def InP (L : Language) : Prop :=
  ∃ (M : DetTM) (t : RunningTime),
    IsPolynomialBound t ∧
    ∀ x, M x = L x

/-- A certificate verifier: takes an input and a certificate, returns Bool -/
def Verifier := Nat → Nat → Bool

/-- Certificate length bound (polynomial) -/
def CertBound (p : RunningTime) : Prop := IsPolynomialBound p

/-- A problem L is in NP: there is a polynomial verifier -/
def InNP (L : Language) : Prop :=
  ∃ (V : Verifier) (p : RunningTime),
    IsPolynomialBound p ∧
    ∀ x, L x = true ↔ ∃ cert, cert ≤ p x ∧ V x cert = true

/- ## The Paper's Central Observations -/

/-
  Observation 2.1 (from the paper): For L ∈ P, the accepting witness is
  the unique deterministic computation path — there is no search required.

  Observation 2.2 (from the paper): For L ∈ NP, the accepting witness is
  a certificate that must be searched for among exponentially many candidates
  of polynomial length.
-/

/-- Number of certificates of length ≤ p for a binary-encoded certificate -/
def numCertificates (p : Nat) : Nat := 2 ^ p

/-- The certificate search space is exponential in the certificate length bound -/
theorem certificate_space_exponential (p : Nat) :
    ¬ IsPolynomialBound numCertificates := by
  intro ⟨c, k, _hc, _hk, h⟩
  -- 2^p grows faster than any c * p^k
  -- This would require a proof that exponential beats polynomial
  -- which is true but requires careful induction
  sorry
  -- NOTE: This part of the paper's argument is CORRECT: the certificate
  -- search space is indeed exponential. The error is in the NEXT step.

/- ## The Paper's Main (Flawed) Inference -/

/-
  The paper's argument (paraphrased):
  "Since the certificate search space is exponential, no polynomial-time
   deterministic algorithm can search it, so NP problems are not in P."

  This looks plausible, but it conflates:
  - The size of the SEARCH SPACE (exponential)
  - The time needed to DECIDE membership (unknown)

  A polynomial-time algorithm for an NP-complete problem would NOT enumerate
  all certificates — it would use structure/insight to find one directly.
  The paper's argument assumes such structural insight is impossible,
  which is exactly what P ≠ NP means and what needs to be proved.
-/

/-- The paper's claimed theorem: P ≠ NP -/
theorem wen_lin_main_claim : ∀ (L : Language), InNP L → ¬ InP L := by
  -- This is exactly the claim P ≠ NP, which is an open problem.
  -- The paper asserts this follows from the exponential certificate space,
  -- but that inference requires additional argument the paper does not provide.
  -- We cannot complete this proof because P ≠ NP is unproven.
  sorry
  -- NOTE: `sorry` here represents the fundamental gap in the paper's argument.
  -- The existence of an exponential certificate space does NOT directly prove
  -- that no polynomial-time algorithm can decide the problem, because a
  -- polynomial-time algorithm need not enumerate all certificates.

/-- Weaker version: the paper's argument shows the *naive search* is exponential -/
def naiveSearch (V : Verifier) (p : RunningTime) (x : Nat) : Bool :=
  -- Enumerate all certificates up to p(x) and check each
  -- This runs in time O(2^p(x) * p(x)) — exponential
  let bound := p x
  (List.range (2 ^ bound)).any (fun cert => V x cert)

/-- The naive search algorithm takes exponential time -/
def naiveSearchTime (p : RunningTime) (x : Nat) : Nat :=
  2 ^ (p x) * p x

/-- The naive search time is not polynomial -/
theorem naive_search_not_polynomial (p : RunningTime) (hp : IsPolynomialBound p) :
    ¬ IsPolynomialBound (naiveSearchTime p) := by
  -- 2^p(x) * p(x) grows exponentially
  -- This is true but requires careful proof
  sorry
  -- NOTE: This part is correct — naive enumeration IS exponential.
  -- The paper's error is claiming this proves NO algorithm can do better.

/- ## Summary of the Paper's Logic -/

/-
  The paper's argument chain (formalized):

  Step 1: Certificate space for NP has size 2^p(|x|)  — TRUE (proved above with sorry)
  Step 2: Naive search requires 2^p(|x|) steps         — TRUE
  Step 3: Therefore no poly-time algorithm exists       — UNJUSTIFIED (requires P ≠ NP)

  The gap between Step 2 and Step 3 is the entire P vs NP problem.
  The paper treats Step 3 as following from Steps 1–2, but it does not.
-/

end WenLinProof
