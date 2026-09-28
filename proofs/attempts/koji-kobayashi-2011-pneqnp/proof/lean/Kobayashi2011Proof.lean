/-
  Forward formalization of Koji Kobayashi's 2011 proof attempt.

  The original paper claims:
    NP > AL = P > NC > NL > L.

  This file follows the paper's intended proof skeleton. The critical
  lower-bound steps are axiomatized because the paper does not provide
  machine-independent proofs of them.
-/

namespace Kobayashi2011ProofAttempt

def Language := String → Prop

structure ComplexityClass where
  contains : Language → Prop

def InClass (C : ComplexityClass) (L : Language) : Prop :=
  C.contains L

def StrictContains (A B : ComplexityClass) : Prop :=
  (∀ L, InClass B L → InClass A L) ∧ ∃ W, InClass A W ∧ ¬ InClass B W

axiom NP : ComplexityClass
axiom AL : ComplexityClass
axiom P : ComplexityClass
axiom NC : ComplexityClass
axiom NL : ComplexityClass
axiom LOGSPACE : ComplexityClass

-- Kobayashi uses the standard identity AL = P.
axiom AL_eq_P : ∀ X, InClass AL X ↔ InClass P X

-- Standard containments used by the final chain.
axiom P_subset_NP : ∀ X, InClass P X → InClass NP X
axiom NC_subset_P : ∀ X, InClass NC X → InClass P X
axiom NL_subset_NC : ∀ X, InClass NL X → InClass NC X
axiom L_subset_NL : ∀ X, InClass LOGSPACE X → InClass NL X

axiom CHAOS : Language
axiom ORDER : Language
axiom LAYER : Language
axiom TWINE : Language

/-
  Original claim: CHAOS is in NP because an NTM guesses the values of all
  element problems, but CHAOS is not in AL because a log-space alternating
  machine allegedly cannot remove cyclic dependency structure.

  Gap: the non-membership claim argues against a particular materialization of
  dependencies, not against every alternating log-space algorithm.
-/
axiom chaos_in_np : InClass NP CHAOS
axiom chaos_not_in_al : ¬ InClass AL CHAOS

/-
  Original claim: ORDER is in P by sequential evaluation, but not in NC because
  parallel evaluation allegedly cannot avoid exponential combinations.

  Gap: this does not exclude all polylog-depth polynomial-size circuits.
-/
axiom order_in_p : InClass P ORDER
axiom order_not_in_nc : ¬ InClass NC ORDER

/-
  Original claim: LAYER is in NC by parallel antichain evaluation, but not in NL
  because an LNTM allegedly cannot record all blocking combinations.

  Gap: this assumes a specific bookkeeping strategy for nondeterministic
  log-space computation.
-/
axiom layer_in_nc : InClass NC LAYER
axiom layer_not_in_nl : ¬ InClass NL LAYER

/-
  Original claim: TWINE is in NL by following one path nondeterministically, but
  not in L because an LDTM allegedly cannot compare all rotate paths.

  Gap: this is not a lower bound against all deterministic log-space algorithms.
-/
axiom twine_in_nl : InClass NL TWINE
axiom twine_not_in_l : ¬ InClass L TWINE

theorem kobayashi_claim_np_strictly_contains_al : StrictContains NP AL := by
  constructor
  · intro X hAL
    exact P_subset_NP X ((AL_eq_P X).mp hAL)
  · exact ⟨CHAOS, chaos_in_np, chaos_not_in_al⟩

theorem kobayashi_claim_p_strictly_contains_nc : StrictContains P NC := by
  constructor
  · intro X hNC
    exact NC_subset_P X hNC
  · exact ⟨ORDER, order_in_p, order_not_in_nc⟩

theorem kobayashi_claim_nc_strictly_contains_nl : StrictContains NC NL := by
  constructor
  · intro X hNL
    exact NL_subset_NC X hNL
  · exact ⟨LAYER, layer_in_nc, layer_not_in_nl⟩

theorem kobayashi_claim_nl_strictly_contains_l : StrictContains NL LOGSPACE := by
  constructor
  · intro X hL
    exact L_subset_NL X hL
  · exact ⟨TWINE, twine_in_nl, twine_not_in_l⟩

/-
  This theorem captures the intended final conclusion. It is only as strong as
  the four axiomatized lower bounds above.
-/
theorem kobayashi_claim_chain :
    StrictContains NP AL ∧ StrictContains P NC ∧
    StrictContains NC NL ∧ StrictContains NL LOGSPACE := by
  exact ⟨kobayashi_claim_np_strictly_contains_al,
         kobayashi_claim_p_strictly_contains_nc,
         kobayashi_claim_nc_strictly_contains_nl,
         kobayashi_claim_nl_strictly_contains_l⟩

#check kobayashi_claim_chain

end Kobayashi2011ProofAttempt
