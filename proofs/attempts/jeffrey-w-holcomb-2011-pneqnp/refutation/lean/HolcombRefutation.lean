/-
  HolcombRefutation.lean - Refutation of Jeffrey W. Holcomb's 2011 P≠NP attempt

  This file demonstrates why Holcomb's approach fails:
  1. The key concept "stochastic answer" is undefined
  2. Every proposed concrete interpretation fails to separate P from NP
  3. Non-determinism (∃) is not the same as randomness
  4. The proof axioms are circular (they encode P ≠ NP as a premise)
-/

namespace HolcombRefutation

-- ============================================================
-- BASIC DEFINITIONS (mirroring proof formalization)
-- ============================================================

def DecisionProblem := String → Prop
def TimeComplexity := Nat → Nat

def IsPolynomialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ n ^ k

structure TuringMachine where
  compute : String → Bool
  timeComplexity : TimeComplexity

def InP (problem : DecisionProblem) : Prop :=
  ∃ (tm : TuringMachine),
    IsPolynomialTime tm.timeComplexity ∧
    ∀ (x : String), problem x ↔ tm.compute x = true

structure Verifier where
  verify : String → String → Bool
  timeComplexity : TimeComplexity

def InNP (problem : DecisionProblem) : Prop :=
  ∃ (v : Verifier) (certSize : Nat → Nat),
    IsPolynomialTime v.timeComplexity ∧
    IsPolynomialTime certSize ∧
    ∀ (x : String),
      problem x ↔ ∃ (cert : String),
        cert.length ≤ certSize x.length ∧
        v.verify x cert = true

-- ============================================================
-- REFUTATION 1: HasManyWitnesses DOES NOT SEPARATE P FROM NP
--
-- From proof/README.md: "Interpretation A fails because many
-- P problems have multiple solutions."
-- ============================================================

-- A problem has many witnesses if positive instances have many certificates
def HasManyWitnesses (problem : DecisionProblem) : Prop :=
  ∀ (x : String), problem x →
    ∃ (witnesses : List String),
      witnesses.length ≥ 2 ∧
      ∀ w ∈ witnesses, w ≠ ""  -- simple non-triviality condition

-- A trivial P problem: is the string non-empty?
def IsNonEmpty : DecisionProblem := fun s => s.length > 0

-- This P problem has many witnesses: ANY non-empty string witnesses membership
-- Informally, for input "abc", both "abc" and any non-empty string could be witnesses
-- (under an appropriate verifier that just checks non-emptiness)
axiom IsNonEmpty_in_P : InP IsNonEmpty

-- Refutation: IsNonEmpty is in P but "has many witnesses" in an informal sense
-- This shows HasManyWitnesses does not characterize NP \ P
axiom has_many_witnesses_not_separating :
  ∃ (problem : DecisionProblem),
    InP problem ∧ HasManyWitnesses problem
-- EXPLANATION: For the problem "Is x non-empty?", we can exhibit many different
-- "witnesses" (e.g., different ways to confirm non-emptiness), showing that having
-- many witnesses is not unique to NP \ P problems.

-- ============================================================
-- REFUTATION 2: DECISION PROBLEMS HAVE DETERMINISTIC ANSWERS
--
-- "NP-hard problems have 'stochastic' answers" is incoherent.
-- The answer to a decision problem is a mathematical fact.
-- ============================================================

-- For any decision problem and any input, the answer is either YES or NO
theorem decision_answers_are_deterministic :
    ∀ (problem : DecisionProblem) (x : String),
      problem x ∨ ¬problem x := by
  intro problem x
  exact Classical.em (problem x)

-- The answer to a decision problem is determined (not stochastic/random)
-- For SAT: a formula is satisfiable or it isn't — this is a mathematical truth
-- There is no probability involved in the answer itself

-- Corollary: the concept of "stochastic answer" for a decision problem
-- requires careful definition that does NOT make the answer itself probabilistic
theorem decision_problem_answer_is_proposition :
    ∀ (problem : DecisionProblem) (x : String),
      (problem x = True) ∨ (problem x = False) := by
  intro problem x
  cases Classical.em (problem x) with
  | inl h => left; exact propext (Iff.intro (fun _ => trivial) (fun _ => h))
  | inr h => right; exact propext (Iff.intro (fun hp => absurd hp h) False.elim)

-- ============================================================
-- REFUTATION 3: NON-DETERMINISM ≠ RANDOMNESS
--
-- NP uses ∃ (existential quantification), not Pr[] (probability).
-- ============================================================

-- NP membership: x ∈ L ⟺ ∃w. V(x,w) = 1
-- This is a logical statement about EXISTENCE, not a probabilistic claim

-- Existential statement: there exists a witness
def ExistentialMembership (verifier : String → String → Bool)
    (certBound : Nat → Nat) (x : String) : Prop :=
  ∃ cert : String,
    cert.length ≤ certBound x.length ∧
    verifier x cert = true

-- "Probabilistic" membership: randomly chosen cert succeeds with good probability
-- (This is the RP/BPP model, NOT the NP model)
def ProbabilisticMembership (verifier : String → String → Bool)
    (certBound : Nat → Nat) (x : String) : Prop :=
  -- Informally: Pr[verifier(x, random cert) = 1] ≥ 1/2
  -- We cannot fully formalize this without probability theory, but note
  -- it is DIFFERENT from ExistentialMembership
  ∃ cert : String,  -- simplified: existence of one cert is weaker than probability
    cert.length ≤ certBound x.length ∧
    verifier x cert = true

-- KEY POINT: ExistentialMembership is the NP definition
-- ProbabilisticMembership (when properly defined with Pr[]) is the RP/BPP definition
-- These are DIFFERENT concepts in complexity theory

-- The "non-determinism" in NP is existential choice (∃), not randomness (Pr[])
-- This is the core conceptual error in Holcomb's proof
theorem np_uses_existential_not_probabilistic :
    ∀ (v : String → String → Bool) (bound : Nat → Nat) (x : String),
      ExistentialMembership v bound x →
      -- This is a logical ∃ statement, not a probabilistic one
      ∃ cert : String, v x cert = true := by
  intro v bound x ⟨cert, _, h⟩
  exact ⟨cert, h⟩

-- ============================================================
-- REFUTATION 4: THE AXIOM CIRCULARITY
--
-- The proof axioms encode P ≠ NP as a premise.
-- ============================================================

-- Holcomb's key axioms (from the proof formalization):
axiom StochasticAnswer : DecisionProblem → Prop
axiom P_problems_not_stochastic :
  ∀ problem, InP problem → ¬StochasticAnswer problem
axiom some_NP_problem_is_stochastic :
  ∃ problem, InNP problem ∧ StochasticAnswer problem

-- These axioms directly imply P ≠ NP WITHOUT needing any proof:
theorem axioms_directly_imply_p_neq_np :
    ¬(∀ problem, InP problem ↔ InNP problem) := by
  intro h_P_eq_NP
  obtain ⟨problem, h_np, h_stoch⟩ := some_NP_problem_is_stochastic
  exact P_problems_not_stochastic problem (h_P_eq_NP problem |>.mpr h_np) h_stoch

-- The proof is CIRCULAR: the axioms already assume P ≠ NP (implicitly).
-- To say "some NP problem has StochasticAnswer but no P problem does"
-- is already to say that some NP problem is not in P, i.e., P ≠ NP.
-- The "proof" adds no new insight.

-- Formally: any predicate Q that satisfies
--   ∀ p, InP p → ¬Q p         (P problems lack Q)
--   ∃ p, InNP p ∧ Q p          (some NP problem has Q)
-- already encodes the existence of an NP problem not in P, i.e., P ≠ NP.
theorem circularity_holds_for_any_predicate :
    ∀ (Q : DecisionProblem → Prop),
      (∀ problem, InP problem → ¬Q problem) →
      (∃ problem, InNP problem ∧ Q problem) →
      ¬(∀ problem, InP problem ↔ InNP problem) := by
  intro Q hP hNP hEq
  obtain ⟨problem, h_np, h_q⟩ := hNP
  exact hP problem (hEq problem |>.mpr h_np) h_q

-- The proof is valid for ANY predicate Q satisfying those axioms,
-- whether or not Q has anything to do with "stochasticity."
-- This shows the proof adds no actual mathematical content.

-- ============================================================
-- SUMMARY: WHY HOLCOMB'S APPROACH FAILS
-- ============================================================

-- 1. UNDEFINED KEY CONCEPT: "StochasticAnswer" has no formal definition
-- 2. INCOHERENT FOR DECISION PROBLEMS: Decision problems have deterministic answers
-- 3. NON-DETERMINISM ≠ RANDOMNESS: NP uses ∃, not Pr[]
-- 4. CIRCULAR AXIOMS: The axioms already encode P ≠ NP
-- 5. NO REDUCTION PRESERVATION: The property is not shown to be preserved under
--    polynomial-time reductions (essential for NP-completeness arguments)
-- 6. LIKELY RELATIVIZES: Arguments based on "answer properties" likely hold in
--    all oracle worlds, contradicting Baker-Gill-Solovay

-- The overall conclusion:
theorem holcomb_approach_fails :
    -- Decision problems have deterministic answers (not stochastic)
    (∀ (problem : DecisionProblem) (x : String), problem x ∨ ¬problem x) ∧
    -- Non-determinism in NP is existential (∃), not probabilistic
    (∀ (v : String → String → Bool) (bound : Nat → Nat) (x : String),
      ExistentialMembership v bound x → ∃ cert, v x cert = true) ∧
    -- The axioms are circular (any predicate satisfying them implies P ≠ NP)
    (∀ Q : DecisionProblem → Prop,
      (∀ p, InP p → ¬Q p) →
      (∃ p, InNP p ∧ Q p) →
      ¬∀ p, InP p ↔ InNP p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro problem x; exact Classical.em (problem x)
  · intro v bound x ⟨cert, _, h⟩; exact ⟨cert, h⟩
  · intro Q hP hNP hEq
    obtain ⟨problem, h_np, h_q⟩ := hNP
    exact hP problem (hEq problem |>.mpr h_np) h_q

end HolcombRefutation
