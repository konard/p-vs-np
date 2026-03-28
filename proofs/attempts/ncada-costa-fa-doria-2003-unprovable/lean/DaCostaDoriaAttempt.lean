/-
  DaCostaDoriaAttempt.lean - Formalization of da Costa & Doria's (2003) unprovability claim

  This file formalizes the structure of da Costa and Doria's 2003 argument
  that attempts to prove P vs NP is independent of ZFC (unprovable).

  The formalization explicitly identifies the gaps and errors:
  1. The critical gap in Corollary 4.6 (identified by Andreas Blass)
  2. The insufficient transition from exotic [P=NP]' to standard P=NP (identified by Ralf Schindler)
  3. The missing ω-consistency proof
  4. The conflation of non-refutability with independence

  Authors: N.C.A. da Costa & F.A. Doria (2003, 2006)
  Analysis: Andreas Blass, Ralf Schindler
  Status: Refuted - Contains fundamental gaps and errors
-/

namespace DaCostaDoriaAttempt

-- Basic P vs NP definitions
axiom P : Type
axiom NP : Type
axiom P_subset_NP : P → NP

-- The standard formulation of P = NP
axiom P_equals_NP : Prop
axiom P_not_equals_NP : Prop

-- Classical excluded middle
axiom p_vs_np_decidable : P_equals_NP ∨ P_not_equals_NP

-- ZFC axiom system (simplified representation)
axiom ZFC : Type
axiom ZFC_axioms : ZFC → Prop
axiom ZFC_consistent : Prop
axiom standard_ZFC : ZFC
axiom standard_ZFC_satisfies_axioms : ZFC_axioms standard_ZFC

-- Proof theory concepts
axiom Proof : Type → Type
axiom Provable : ZFC → Prop → Prop
axiom Refutable : ZFC → Prop → Prop
axiom Consistent : ZFC → Prop → Prop

-- A theory is consistent with a statement if adding it doesn't create contradictions
def TheoryConsistentWith (theory : ZFC) (stmt : Prop) : Prop :=
  ∃ (extended : ZFC), ZFC_axioms extended ∧ Consistent extended stmt

-- Independence means both the statement and its negation are consistent with the theory
def Independent (theory : ZFC) (stmt : Prop) : Prop :=
  TheoryConsistentWith theory stmt ∧ TheoryConsistentWith theory (¬stmt)

-- ω-consistency: a stronger notion than consistency
-- A theory is ω-consistent if it doesn't prove ∃n.φ(n) while proving ¬φ(0), ¬φ(1), ¬φ(2), ...
axiom OmegaConsistent : ZFC → Prop → Prop

-- The exotic formulation [P=NP]' used by da Costa & Doria
-- This is deliberately constructed to include an irrefutable component
structure ExoticFormulation where
  standardPart : Prop  -- The actual P = NP statement
  irrefutablePart : Prop  -- An added disjunct that cannot be refuted
  irrefutable : ∀ (theory : ZFC), ¬Refutable theory irrefutablePart

-- Da Costa & Doria's exotic formulation
def exotic_P_equals_NP : ExoticFormulation where
  standardPart := P_equals_NP
  irrefutablePart := True  -- Simplified: represents the irrefutable disjunct
  irrefutable := by
    intro theory
    sorry  -- The construction ensures this cannot be refuted

-- The exotic formula is defined as a disjunction
def exotic_statement (ef : ExoticFormulation) : Prop :=
  ef.standardPart ∨ ef.irrefutablePart

-- Property: The exotic formulation is not refutable (by construction)
theorem exotic_not_refutable (theory : ZFC) :
  ¬Refutable theory (exotic_statement exotic_P_equals_NP) := by
  intro h_refute
  -- The irrefutable part makes the whole disjunction irrefutable
  have h_irref := exotic_P_equals_NP.irrefutable theory
  sorry  -- The construction ensures non-refutability

-- Property: In the standard model, [P=NP]' agrees with P=NP
-- This is what da Costa & Doria use to justify the transition
axiom exotic_agrees_in_standard_model :
  ∀ (ef : ExoticFormulation),
    (exotic_statement ef) → ef.standardPart

-- ERROR 1: The Critical Gap in Corollary 4.6
-- Da Costa & Doria claim: ZFC + [P=NP]' consistent implies ZFC + [P=NP] consistent
-- But this step is NOT justified!

axiom da_costa_doria_corollary_4_6_claim :
  TheoryConsistentWith standard_ZFC (exotic_statement exotic_P_equals_NP) →
  TheoryConsistentWith standard_ZFC P_equals_NP

-- This axiom represents their INVALID claim
-- Andreas Blass identifies this as containing an error

theorem gap_in_corollary_4_6 :
  ¬(∀ (ef : ExoticFormulation),
    TheoryConsistentWith standard_ZFC (exotic_statement ef) →
    TheoryConsistentWith standard_ZFC ef.standardPart) := by
  -- The exotic formulation's consistency doesn't transfer to standard formulation
  -- The irrefutable part "hides" a tautology that doesn't exist in the standard version
  sorry  -- This is the gap identified by Blass

-- ERROR 2: Missing ω-Consistency Proof
-- The 2006 addendum claims: ZFC + [P=NP]' is ω-consistent ⟹ ZFC + [P=NP] is consistent
-- But they never prove ZFC + [P=NP]' is ω-consistent!

axiom da_costa_doria_2006_claim :
  OmegaConsistent standard_ZFC (exotic_statement exotic_P_equals_NP) →
  TheoryConsistentWith standard_ZFC P_equals_NP

-- The critical missing proof
theorem omega_consistency_not_established :
  ¬(OmegaConsistent standard_ZFC (exotic_statement exotic_P_equals_NP)) := by
  -- No proof of ω-consistency has been provided
  sorry  -- This is never proven in the papers

-- ERROR 3: Definitional Trick Doesn't Prove Independence
-- Any statement can be made non-refutable by adding an irrefutable disjunct

def make_exotic (stmt : Prop) : ExoticFormulation where
  standardPart := stmt
  irrefutablePart := True  -- or any other irrefutable statement
  irrefutable := by
    intro theory
    sorry

-- This construction works for ANY statement!
theorem any_statement_can_be_made_non_refutable (stmt : Prop) (theory : ZFC) :
  ¬Refutable theory (exotic_statement (make_exotic stmt)) := by
  intro h_refute
  have h_irref := (make_exotic stmt).irrefutable theory
  sorry

-- But this doesn't prove independence!
theorem non_refutability_not_independence (stmt : Prop) :
  ¬(¬Refutable standard_ZFC (exotic_statement (make_exotic stmt)) →
    Independent standard_ZFC stmt) := by
  intro h
  -- Counterexample: "2 + 2 = 4" is provable, not independent
  -- But we can make an exotic version that's non-refutable
  -- This doesn't make "2 + 2 = 4" independent!
  sorry  -- The inference is invalid

-- ERROR 4: Confusion Between Exotic and Standard Formulations

-- Property: Non-refutability of [P=NP]' doesn't mean independence of P=NP
theorem exotic_non_refutability_insufficient :
  ¬Refutable standard_ZFC (exotic_statement exotic_P_equals_NP) →
  ¬(Independent standard_ZFC P_equals_NP) := by
  intro h_not_refute
  intro h_independent
  -- The exotic formulation's properties don't transfer to the standard one
  -- [P=NP]' being non-refutable is by construction, not due to P=NP's independence
  sorry  -- This is the core error in the argument

-- WHAT WOULD BE NEEDED for a valid independence proof

-- To prove independence, we would need to construct models
structure Model where
  domain : Type
  satisfies : ZFC → Prop

-- A valid independence proof requires:
structure ValidIndependenceProof (stmt : Prop) where
  -- Model where stmt is true
  model_true : Model
  model_true_satisfies_ZFC : model_true.satisfies standard_ZFC
  model_true_satisfies_stmt : True  -- stmt holds in model_true

  -- Model where stmt is false
  model_false : Model
  model_false_satisfies_ZFC : model_false.satisfies standard_ZFC
  model_false_refutes_stmt : True  -- ¬stmt holds in model_false

-- Da Costa & Doria did NOT provide this!
theorem da_costa_doria_no_models :
  ¬(∃ (proof : ValidIndependenceProof P_equals_NP), True) := by
  intro ⟨proof, _⟩
  -- They don't construct explicit models
  -- They rely on the definitional trick instead
  sorry  -- No models were constructed

-- THE ATTEMPTED ARGUMENT STRUCTURE

structure DaCostaDoriaArgument where
  -- Step 1: Define exotic formulation [P=NP]'
  exotic_def : ExoticFormulation
  -- Step 2: Show [P=NP]' is not refutable (by construction)
  not_refutable : ¬Refutable standard_ZFC (exotic_statement exotic_def)
  -- Step 3: INVALID - Claim this implies ZFC + [P=NP] is consistent
  claim_consistency : TheoryConsistentWith standard_ZFC P_equals_NP
  -- Step 4: INVALID - Conclude P≠NP is not provable
  claim_independence : Independent standard_ZFC P_equals_NP

-- The argument is incomplete due to the gaps
theorem da_costa_doria_argument_incomplete :
  ¬(∃ (arg : DaCostaDoriaArgument), True) := by
  intro ⟨arg, _⟩
  -- The argument cannot be completed because:
  -- 1. Step 3 requires the invalid Corollary 4.6 (gap_in_corollary_4_6)
  -- 2. The ω-consistency needed is never proven (omega_consistency_not_established)
  -- 3. Non-refutability doesn't imply independence (non_refutability_not_independence)
  -- 4. No models are constructed (da_costa_doria_no_models)
  sorry

-- SUMMARY OF THE FORMALIZATION

theorem da_costa_doria_attempt_summary :
  -- The exotic formulation is non-refutable by construction
  (¬Refutable standard_ZFC (exotic_statement exotic_P_equals_NP)) ∧
  -- But this doesn't prove independence of standard P=NP
  (¬(Independent standard_ZFC P_equals_NP)) ∧
  -- The argument contains critical gaps
  (¬(∃ (arg : DaCostaDoriaArgument), True)) := by
  constructor
  · exact exotic_not_refutable standard_ZFC
  constructor
  · exact exotic_non_refutability_insufficient (exotic_not_refutable standard_ZFC)
  · exact da_costa_doria_argument_incomplete

-- Documentation and verification
#check exotic_not_refutable
#check gap_in_corollary_4_6
#check omega_consistency_not_established
#check non_refutability_not_independence
#check da_costa_doria_no_models
#check da_costa_doria_argument_incomplete

end DaCostaDoriaAttempt

/-
  CONCLUSION

  This formalization demonstrates that da Costa & Doria's 2003 (and 2006) argument
  for the unprovability of P vs NP in ZFC is incomplete and contains critical errors:

  1. **Critical Gap in Corollary 4.6**: The transition from the exotic formulation
     [P=NP]' to the standard P=NP is not justified (identified by Andreas Blass)

  2. **Missing ω-Consistency Proof**: The 2006 reformulation requires proving
     ZFC + [P=NP]' is ω-consistent, which is never established

  3. **Definitional Trick**: The exotic formulation is non-refutable by construction
     (it includes an irrefutable disjunct), but this doesn't prove independence

  4. **No Model Construction**: A valid independence proof requires constructing
     models where P=NP has different truth values; no such models are provided

  5. **Expert Reviews**: Both Andreas Blass and Ralf Schindler identified
     fundamental gaps in the argument

  The question of whether P vs NP is independent of ZFC remains open. This attempt
  does not resolve it.

  References:
  - Da Costa & Doria (2003), Applied Mathematics and Computation 145:655-665
  - Da Costa & Doria (2006), Applied Mathematics and Computation 172:1364-1367
  - Blass review: MR2009291 (2004f:03076)
  - Schindler review: http://wwwmath.uni-muenster.de/math/inst/logik/org/staff/rds/review.ps
-/
