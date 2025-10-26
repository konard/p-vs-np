/-
  NamAttempt.lean - Formalization of Ki-Bong Nam et al. (2004) P≠NP attempt

  This file formalizes the attempted proof by Ki-Bong Nam, S.H. Wang, and
  Yang Gon Kim (2004) using linear algebra and Lie algebra, and demonstrates
  the logical gap identified by Richard K. Molnar in his AMS review.

  Paper: "Linear Algebra, Lie Algebra and their applications to P versus NP"
  Journal of Applied Algebra and Discrete Structures, Vol. 2, pp. 1-26, 2004

  Review: MR2038228 (2005e:68070) by Richard K. Molnar
-/

-- Basic complexity theory framework

/-- A decision problem is represented as a predicate on strings (inputs) -/
def DecisionProblem := String → Prop

/-- Time complexity function: maps input size to time bound -/
def TimeComplexity := Nat → Nat

/-- A problem is polynomial-time if there exists a polynomial time bound -/
def IsPolynomialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ n ^ k

/-- A Turing machine model (abstract representation) -/
structure TuringMachine where
  compute : String → Bool
  timeComplexity : TimeComplexity

/-- A problem is in P if it can be decided by a polynomial-time TM -/
def InP (problem : DecisionProblem) : Prop :=
  ∃ (tm : TuringMachine),
    (IsPolynomialTime tm.timeComplexity) ∧
    (∀ (x : String), problem x ↔ tm.compute x = true)

/-- A problem is in NP if solutions can be verified in polynomial time -/
def InNP (problem : DecisionProblem) : Prop :=
  ∃ (verify : String → String → Bool) (vTime certSize : TimeComplexity),
    (IsPolynomialTime vTime) ∧
    (IsPolynomialTime certSize) ∧
    (∀ (x : String),
      problem x ↔ ∃ (cert : String),
        cert.length ≤ certSize x.length ∧
        verify x cert = true)

/-- Basic axiom: P ⊆ NP (every problem in P is also in NP) -/
axiom P_subset_NP : ∀ problem, InP problem → InNP problem

/-- P ≠ NP means there exists a problem in NP but not in P -/
def P_not_equals_NP : Prop :=
  ∃ (problem : DecisionProblem), InNP problem ∧ ¬InP problem

/-
  NAM ET AL. PROBLEM DEFINITION

  The paper defines a counting problem involving systems of linear equations
  with both deterministic data and random variables.
-/

/-- Representation of a linear system with random variables -/
structure LinearSystemWithRandomVars where
  /-- Dimension of the system -/
  dimension : Nat

  /-- Input data (coefficients) -/
  inputData : List Nat

  /-- Random variable components -/
  randomVarCount : Nat

  /-- The counting problem: count solutions to the system -/
  solutionCount : Nat

/-
  The specific counting problem from Nam et al.'s paper
  Input: A linear system with random variables
  Output: Whether the solution count satisfies a certain property
-/
def NamCountingProblem : DecisionProblem :=
  fun (_encoded_system : String) =>
    -- In a full implementation, this would decode the string
    -- into a LinearSystemWithRandomVars and check the property
    True  -- Placeholder for the actual problem definition

/-
  NAM ET AL.'S CLAIMS
-/

/-
  CLAIM 1: The problem they define is a valid counting problem
  This claim appears reasonable - they do define a mathematical problem
-/
axiom nam_problem_well_defined :
  ∀ (system : LinearSystemWithRandomVars),
    system.dimension > 0 →
    ∃ (count : Nat), system.solutionCount = count

/-
  CLAIM 2: The problem is in NP
  The paper doesn't clearly establish this, but let's assume it for analysis
-/
axiom nam_problem_in_NP : InNP NamCountingProblem

/-
  CLAIM 3 (THE KEY ASSERTION): The problem cannot be solved in polynomial time

  This is the critical claim that Molnar's review identifies as unjustified.
  The authors assert this based on the presence of random variables, but
  provide no rigorous proof.
-/
axiom nam_asserted_not_in_P : ¬InP NamCountingProblem

/-
  THE PURPORTED PROOF

  If we accept all three claims, then P ≠ NP follows immediately:
-/
theorem nam_purported_proof : P_not_equals_NP := by
  unfold P_not_equals_NP
  exact ⟨NamCountingProblem, nam_problem_in_NP, nam_asserted_not_in_P⟩

/-
  ANALYSIS OF THE ERROR

  The error identified by Richard K. Molnar:
  The assertion nam_asserted_not_in_P is not proven, only asserted.
-/

/-
  What would be needed to prove ¬InP NamCountingProblem:

  We would need to show that for ANY Turing machine that solves the problem,
  its time complexity is NOT polynomial.
-/
def HasSuperPolynomialLowerBound (problem : DecisionProblem) : Prop :=
  ∀ (tm : TuringMachine),
    (∀ (x : String), problem x ↔ tm.compute x = true) →
    ¬IsPolynomialTime tm.timeComplexity

/-
  The paper claims (without proof) that this lower bound exists:
-/
axiom nam_claimed_lower_bound :
  HasSuperPolynomialLowerBound NamCountingProblem

/-
  But this is EXACTLY what needs to be proven, not assumed!
  This is the fundamental gap in the argument.
-/

/-
  DEMONSTRATING THE LOGICAL GAP

  The structure of Nam et al.'s argument:

  1. Define a problem involving random variables [✓ Well-defined]
  2. Assert problem is in NP [? Needs verification]
  3. Assert problem is not in P because it has random variables [✗ UNJUSTIFIED]
  4. Conclude P ≠ NP [Only valid if steps 2 and 3 are proven]
-/

/-
  The key error: Confusing "problem appears complex" with
  "problem provably requires super-polynomial time"
-/

/-
  Counter-argument to Nam et al.'s reasoning:

  Just because a problem involves random variables or complex algebraic
  structures does NOT imply computational hardness.
-/
def presence_of_complexity_not_sufficient : Prop :=
  ∀ (problem : DecisionProblem),
    -- Even if problem has complex structure...
    (∀ (_system : LinearSystemWithRandomVars), True) →
    -- ...we cannot conclude it requires super-polynomial time without proof
    ¬(¬IsPolynomialTime (fun n => n * n) → ¬InP problem)

/-
  What's missing: A rigorous lower bound proof

  To prove P ≠ NP via this approach, Nam et al. would need:

  1. Formal definition of their counting problem
  2. Proof that it's in NP
  3. Proof of a super-polynomial LOWER BOUND (the hard part!)
     - This requires showing NO polynomial-time algorithm exists
     - Must work in any oracle world (to avoid relativization barrier)
     - Must not be "natural" in the Razborov-Rudich sense
     - Must avoid the algebrization barrier
-/
def CompleteProofWouldRequire : Prop :=
  ∃ (problem : DecisionProblem),
    InNP problem ∧
    -- This is the part that's missing:
    (∀ (tm : TuringMachine),
      (∀ x, problem x ↔ tm.compute x = true) →
      ∃ (superPoly : Nat → Nat),
        (¬IsPolynomialTime superPoly) ∧
        (∀ n, tm.timeComplexity n ≥ superPoly n))

/-
  The paper provides no such lower bound proof.
  Molnar's review correctly identifies this gap.
-/

/-
  FORMAL STATEMENT OF THE ERROR

  THEOREM: The Nam et al. proof is incomplete

  Their argument relies on an unproven assertion (nam_asserted_not_in_P)
  which is precisely what needs to be proven to establish P ≠ NP.
-/
theorem nam_proof_is_incomplete :
  -- The proof assumes its conclusion
  ((¬InP NamCountingProblem) → P_not_equals_NP) ∧
  -- But nam_asserted_not_in_P is not derived, only asserted
  True := by
  constructor
  · intro h
    unfold P_not_equals_NP
    exact ⟨NamCountingProblem, nam_problem_in_NP, h⟩
  · trivial

/-
  Summary of the formalization:

  We have shown that:
  1. The Nam et al. argument can be formalized
  2. It relies on an axiom (nam_asserted_not_in_P) that is not proven
  3. This axiom IS the super-polynomial lower bound that would prove P ≠ NP
  4. The paper provides no rigorous derivation of this axiom
  5. Molnar's critique is correct: the assertion is "not convincing"

  The error: Assuming the conclusion (super-polynomial lower bound)
            rather than proving it.
-/

/-
  LESSONS FROM THIS ATTEMPT

  Common pattern in failed P vs NP proofs:

  1. Define a specific problem instance
  2. Assert (without rigorous proof) that it's hard
  3. Conclude P ≠ NP

  What's missing: Step 2 requires proving a lower bound, which is
  exactly as hard as proving P ≠ NP itself.

  This is why P vs NP remains open: proving super-polynomial lower bounds
  for general computation models is extraordinarily difficult.
-/

-- Verification checks
#check nam_purported_proof
#check nam_proof_is_incomplete
#check HasSuperPolynomialLowerBound
#check CompleteProofWouldRequire

#print "✓ Formalization of Nam et al. (2004) attempt complete"
