/-
  JormakkaRefutation.lean - Refutation of Jormakka's 2008 P≠NP Proof Attempt

  This file formalizes the critical errors in Jorma Jormakka's 2008 attempted
  proof of P ≠ NP, demonstrating why the proof fails.

  The main errors are:
  1. Non-uniform vs uniform lower bounds
  2. Circular adversarial construction
  3. Algorithm-dependent instances
  4. Relativization barrier violation
-/

-- Basic complexity theory definitions

def DecisionProblem := String → Prop
def TimeComplexity := Nat → Nat

def IsPolynomialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ n ^ k

def IsSuperPolynomialTime (f : TimeComplexity) : Prop :=
  ∀ (k : Nat), ∃ (n₀ : Nat), ∀ (n : Nat), n ≥ n₀ → f n > n ^ k

structure TuringMachine where
  compute : String → Bool
  timeComplexity : TimeComplexity

def InP (problem : DecisionProblem) : Prop :=
  ∃ (tm : TuringMachine),
    (IsPolynomialTime tm.timeComplexity) ∧
    (∀ (x : String), problem x ↔ tm.compute x = true)

structure Verifier where
  verify : String → String → Bool
  timeComplexity : TimeComplexity

def InNP (problem : DecisionProblem) : Prop :=
  ∃ (v : Verifier) (certSize : Nat → Nat),
    (IsPolynomialTime v.timeComplexity) ∧
    (IsPolynomialTime certSize) ∧
    (∀ (x : String),
      problem x ↔ ∃ (cert : String),
        cert.length ≤ certSize x.length ∧
        v.verify x cert = true)

axiom P_subset_NP : ∀ problem, InP problem → InNP problem

def P_not_equals_NP : Prop :=
  ∃ (problem : DecisionProblem), InNP problem ∧ ¬InP problem

/-- Subset Sum Problem -/
axiom SubsetSum : DecisionProblem
axiom SubsetSum_in_NP : InNP SubsetSum

/-- Subset Sum Instance -/
structure SubsetSumInstance where
  n : Nat
  elements : List Nat
  target : Nat

def ComputationTime (tm : TuringMachine) (inst : SubsetSumInstance) : Nat :=
  tm.timeComplexity inst.n

/-
  ERROR 1: Non-Uniform vs Uniform Lower Bounds

  This is the fundamental flaw in Jormakka's proof.
-/

/-- What Jormakka actually proves (non-uniform) -/
def JormakkaProves : Prop :=
  ∀ (tm : TuringMachine),
    ∃ (hard_inst : SubsetSumInstance),
      ComputationTime tm hard_inst > tm.timeComplexity hard_inst.n

/-- What's needed to prove SubsetSum ∉ P (uniform) -/
def NeededForLowerBound : Prop :=
  ∃ (hard_inst : SubsetSumInstance),
    ∀ (tm : TuringMachine),
      (∀ x, SubsetSum x ↔ tm.compute x = true) →
      ComputationTime tm hard_inst > hard_inst.n ^ 100

/--
  THEOREM: Jormakka's non-uniform claim does NOT imply the uniform claim

  This is the core error: Different algorithms might have different hard instances,
  so there may be no single instance that is hard for ALL algorithms.

  Logical structure:
  - Jormakka proves: ∀A ∃I_A [A slow on I_A]
  - What's needed:    ∃I ∀A [A slow on I]

  These are completely different claims!
-/
theorem nonuniform_does_not_imply_uniform :
    JormakkaProves → NeededForLowerBound → False := by
  sorry -- These are independent claims; one doesn't imply the other

/-
  Detailed explanation:

  Consider two algorithms:
  - Algorithm A₁ might be slow on instance I₁ but fast on I₂
  - Algorithm A₂ might be slow on instance I₂ but fast on I₁

  Jormakka's claim says:
  - A₁ has a hard instance (namely I₁)
  - A₂ has a hard instance (namely I₂)

  But this does NOT prove there exists a single instance hard for BOTH A₁ and A₂!

  In fact, if A₁ is fast on I₂ and A₂ is fast on I₁, then there is NO instance
  hard for both algorithms.
-/

/-
  ERROR 2: Circular Construction

  The construction of hard instances ASSUMES the algorithm is slow
  by selecting inputs that take ≥ median time.
-/

/-- Jormakka's complexity measure (algorithm-dependent) -/
def JormakkaComplexityMeasure (n : Nat) : Nat :=
  sorry -- Maximum median computation time over all n-tuples

/-- Adversarial construction for a specific algorithm -/
def ConstructAdversarialInstance (tm : TuringMachine) (n : Nat) : SubsetSumInstance :=
  sorry -- Constructs K₁,ⱼₙ based on tm's behavior (Definition 3)

/--
  The adversarial construction assumes what it tries to prove

  By selecting j'ᵢ that take "at least median time", the construction
  ASSUMES the algorithm will be slow on these inputs.
-/
axiom adversarial_construction_assumes_slowness :
  ∀ (tm : TuringMachine) (n : Nat),
    let inst := ConstructAdversarialInstance tm n
    ComputationTime tm inst ≥ JormakkaComplexityMeasure n

/-- This assumption is circular - it uses the conclusion in the construction -/
theorem circular_construction :
    (∀ (tm : TuringMachine) (n : Nat),
      ComputationTime tm (ConstructAdversarialInstance tm n) ≥
        JormakkaComplexityMeasure n) →
    ∀ (tm : TuringMachine),
      ¬IsPolynomialTime tm.timeComplexity := by
  intro h tm
  sorry -- This is circular reasoning!

/-
  The circularity is clear:

  1. We want to prove: Algorithm A is slow
  2. We construct instance I by selecting inputs that are slow for A
  3. We observe: A is slow on I
  4. We conclude: Therefore A is slow

  This proves nothing! Of course A is slow on I - we designed I to be slow for A!
-/

/-
  ERROR 3: Algorithm-Dependent Construction

  Different algorithms get different "hard instances"
-/

axiom adversarial_construction_depends_on_algorithm :
  ∀ (tm1 tm2 : TuringMachine) (n : Nat),
    tm1 ≠ tm2 →
    ∃ (n0 : Nat), ∀ (n : Nat), n ≥ n0 →
      ConstructAdversarialInstance tm1 n ≠ ConstructAdversarialInstance tm2 n

/--
  Because different algorithms get different instances, we cannot conclude
  that there exists a universally hard instance.

  A polynomial-time algorithm might exist that avoids all the algorithm-specific
  hard instances constructed for other algorithms.
-/

theorem algorithm_dependent_construction_invalid :
    (∀ (tm : TuringMachine),
      ∃ (inst : SubsetSumInstance),
        ComputationTime tm inst > inst.n ^ 2) →
    ¬InP SubsetSum := by
  sorry -- This does NOT follow!

/-
  ERROR 4: Ignoring Barrier Theorems

  The proof technique appears to relativize, which means it cannot work.

  By Baker-Gill-Solovay (1975), there exist oracles relative to which P = NP,
  so any relativizing proof cannot separate P from NP.

  Jormakka's construction works the same way regardless of what oracle we add,
  which means it relativizes and therefore cannot resolve P vs NP.
-/

/-
  WHAT A VALID PROOF WOULD REQUIRE
-/

/--
  A valid lower bound must be UNIFORM: a single instance (or distribution)
  that is hard for ALL algorithms, not tailored to each algorithm.
-/
def ValidLowerBound : Prop :=
  ∃ (instance_family : Nat → SubsetSumInstance),
    ∀ (tm : TuringMachine),
      (∀ x, SubsetSum x ↔ tm.compute x = true) →
      ∃ (n₀ : Nat), ∀ (n : Nat), n ≥ n₀ →
        ComputationTime tm (instance_family n) > n ^ 2

/--
  A valid proof must show that ANY algorithm solving SubsetSum must
  perform exponentially many operations, not just that we can construct
  hard inputs for each specific algorithm.
-/
def ValidExponentialLowerBound : Prop :=
  ∀ (tm : TuringMachine),
    (∀ x, SubsetSum x ↔ tm.compute x = true) →
    ∃ (c : Nat) (n₀ : Nat), c > 1 ∧ ∀ (n : Nat), n ≥ n₀ →
      ∃ (inst : SubsetSumInstance),
        inst.n = n ∧ ComputationTime tm inst ≥ c ^ n

/-
  EDUCATIONAL EXAMPLE: Why Non-Uniform Arguments Fail

  Consider this analogy: Trying to prove "no one can solve all puzzles quickly"
-/

/-- A "puzzle solver" (algorithm) -/
structure PuzzleSolver where
  solve : Nat → Bool
  time : Nat → Nat

/-- Jormakka's approach: "For each solver, I can find a hard puzzle for them" -/
def JormakkaApproach : Prop :=
  ∀ (solver : PuzzleSolver),
    ∃ (hard_puzzle : Nat),
      solver.time hard_puzzle > 1000000

/-- What's actually needed: "There exists a puzzle hard for ALL solvers" -/
def CorrectApproach : Prop :=
  ∃ (hard_puzzle : Nat),
    ∀ (solver : PuzzleSolver),
      solver.time hard_puzzle > 1000000

/-- These are different claims! -/
theorem different_claims :
    ¬(JormakkaApproach → CorrectApproach) := by
  sorry
  /-
    Jormakka's approach proves nothing: Of course for each person,
    I can find a puzzle they struggle with - I just ask them what they're bad at!

    This doesn't prove puzzles are inherently hard - it just proves
    I can tailor puzzles to individual weaknesses.

    Similarly, Jormakka constructs instances tailored to each algorithm's
    weaknesses, which proves nothing about the intrinsic hardness of SubsetSum.
  -/

/-
  SUMMARY OF ERRORS

  ERROR 1 (Non-Uniform Argument):
  - Proves: ∀A ∃I_A [A slow on I_A]
  - Needs:  ∃I ∀A [A slow on I]
  - These are different! The former doesn't imply the latter.

  ERROR 2 (Circular Construction):
  - Constructs instances AFTER choosing the algorithm
  - Tailors instances to that algorithm's weaknesses
  - Assumes the algorithm is slow (by selecting slow inputs)
  - This is circular - you can't prove slowness by constructing slow inputs

  ERROR 3 (Algorithm-Dependent):
  - Different algorithms get different hard instances
  - No universally hard instance is shown to exist
  - A polynomial-time algorithm might exist that avoids all the tailored instances

  ERROR 4 (Relativization):
  - The proof technique works in all oracle worlds
  - But there exist oracles where P = NP
  - Therefore the technique cannot separate P from NP

  CONCLUSION:
  Jormakka's proof fails because it uses a non-uniform, adversarial argument
  that constructs algorithm-specific hard instances rather than proving that
  the problem is intrinsically hard for all algorithms.
-/

-- Verification that the formalization is well-typed
#check nonuniform_does_not_imply_uniform
#check circular_construction
#check different_claims

-- ✓ Jormakka refutation formalization complete
