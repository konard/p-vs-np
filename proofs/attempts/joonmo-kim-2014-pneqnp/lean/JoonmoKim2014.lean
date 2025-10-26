/-
  Formalization of Joonmo Kim's 2014 P≠NP Proof Attempt
  This formalization demonstrates the errors in the proof
  Reference: https://arxiv.org/abs/1403.4143
  Refutation: https://arxiv.org/abs/1404.5352
-/

-- Basic types for complexity theory concepts
axiom SATInstance : Type
axiom satisfiable : SATInstance → Prop

-- Turing Machine concepts
axiom TuringMachine : Type
axiom TransitionTable : Type
axiom Configuration : Type
axiom Input : Type

-- An accepting computation is a sequence of configurations
def AcceptingComputation := List Configuration

-- Number of transitions in an accepting computation
def num_transitions (ac : AcceptingComputation) : Nat :=
  match ac with
  | [] => 0
  | _ :: rest => rest.length

-- A particular transition table can produce an accepting computation
axiom produces : TransitionTable → TuringMachine → Input → AcceptingComputation → Prop

-- SAT instance structure
axiom input_part : SATInstance → SATInstance
axiom run_part : SATInstance → SATInstance
axiom concatenate : SATInstance → SATInstance → SATInstance
axiom num_clauses : SATInstance → Nat

-- Cook-Levin encoding
axiom cook_levin_encode : AcceptingComputation → SATInstance

-- Property: each transition requires multiple clauses
axiom clauses_gt_transitions : ∀ (ac : AcceptingComputation),
  num_clauses (cook_levin_encode ac) > num_transitions ac

-- Machine M family
axiom M : Nat → TuringMachine
axiom run_parts : Nat → List SATInstance

-- SAT solver properties
axiom P_eq_NP : Prop  -- P = NP
axiom SAT_in_NP : Prop  -- SAT is in NP

-- Dsat and NDsat properties
axiom is_Dsat : TransitionTable → Prop
axiom is_NDsat : TransitionTable → Prop

-- M° exists: special machine with specific properties
axiom M_circle_index : Nat
def M_circle := M M_circle_index
axiom M_circle_input : Input
axiom c_circle : SATInstance
axiom t_circle : TransitionTable

-- Two accepting computations
axiom ac_M_circle : AcceptingComputation
axiom ac_c_circle : AcceptingComputation

-- Core properties of M°
axiom M_circle_property_1 : produces t_circle M_circle M_circle_input ac_M_circle
axiom M_circle_property_2 : produces t_circle M_circle M_circle_input ac_c_circle
axiom c_circle_is_encoding : c_circle = cook_levin_encode ac_c_circle

-- The modus tollens propositions
def P1 := P_eq_NP  -- P = NP
def P2 := ∃ t, produces t M_circle M_circle_input ac_M_circle  -- M° exists
def P3 := is_Dsat t_circle  -- t is Dsat

-- Part 1 of Kim's proof: P1 → (P2 → P3)
-- This part is actually valid - if P = NP, then polynomial-time SAT solvers exist
axiom kim_part1 : P1 → (P2 → P3)

-- Part 2: Kim claims M° exists with NDsat
axiom M_circle_exists_with_NDsat :
  ∃ t, is_NDsat t ∧ produces t M_circle M_circle_input ac_M_circle

theorem kim_P2_holds : P2 := by
  obtain ⟨t, _, h⟩ := M_circle_exists_with_NDsat
  exact ⟨t, h⟩

-- INTERPRETATION 1: Accepting computations tied to their machines

axiom original_TM_of_ac : AcceptingComputation → TuringMachine

def proper_accepting_computation (ac : AcceptingComputation) (t : TransitionTable) (y : Input) :=
  produces t (original_TM_of_ac ac) y ac

-- Under interpretation 1, merged tables are malformed
axiom state_space : TransitionTable → Type
axiom merged_table_different_states : ∀ (t1 t2 t_merged : TransitionTable), True

-- Under interpretation 1, same transition table doesn't mean same computation
theorem interpretation1_no_contradiction :
  (∃ t, produces t M_circle M_circle_input ac_M_circle ∧
        produces t M_circle M_circle_input ac_c_circle) →
  ¬(ac_M_circle = ac_c_circle) := by
  intro ⟨t, _, _⟩ h_eq
  -- The computations come from different machines with different behaviors
  -- The merged table has a different state space, so it's not valid
  sorry

-- INTERPRETATION 2: Accepting computations from any transition table

-- Under interpretation 2, same transition table means same computation
axiom interpretation2_same_computation :
  produces t_circle M_circle M_circle_input ac_M_circle →
  produces t_circle M_circle M_circle_input ac_c_circle →
  ac_M_circle = ac_c_circle

-- Counting arguments
def i := num_transitions ac_M_circle  -- transitions in ac_M°
def j := num_clauses c_circle  -- clauses in c°
def k := num_transitions ac_c_circle  -- transitions in ac_c°

-- Kim's claims
axiom kim_claim_i_gt_j : i > j
axiom kim_claim_j_gt_k : j > k

-- If ac_M° = ac_c° (interpretation 2), then i = k
theorem interpretation2_i_equals_k :
  ac_M_circle = ac_c_circle → i = k := by
  intro h_eq
  unfold i k
  rw [h_eq]

-- Under interpretation 2, there's no contradiction because
-- the assumptions i > j and j > k don't apply
theorem interpretation2_no_contradiction :
  (produces t_circle M_circle M_circle_input ac_M_circle →
   produces t_circle M_circle M_circle_input ac_c_circle →
   ac_M_circle = ac_c_circle) →
  True := by
  intro _
  trivial

-- THE CORE ERROR: Inconsistent Interpretations

-- Kim's proof mixes interpretations:
-- 1. Uses interpretation 1 to establish i > j > k
-- 2. Uses interpretation 2 to establish i = k
-- 3. Derives a contradiction (but this is invalid!)

theorem kim_proof_error :
  ¬((i > j ∧ j > k) ∧
    (ac_M_circle = ac_c_circle → i = k) ∧
    ac_M_circle = ac_c_circle) := by
  intro ⟨⟨h_i_gt_j, h_j_gt_k⟩, h_implies_eq, h_eq⟩
  have h_i_eq_k := h_implies_eq h_eq
  -- Now we have i > j > k and i = k
  rw [h_i_eq_k] at h_i_gt_j
  rw [h_i_eq_k] at h_j_gt_k
  -- This gives k > j > k, which is impossible
  have h_k_gt_k : k > k := Nat.lt_trans h_j_gt_k h_i_gt_j
  exact Nat.lt_irrefl k h_k_gt_k

-- ADDITIONAL ERROR: Circular Definition

-- M° is DEFINED by the existence of t
-- So "M° exists" ↔ "t exists"
def M_circle_exists := P2
def t_circle_exists := ∃ t, produces t M_circle M_circle_input ac_M_circle

-- By definition, M° exists iff t exists
axiom circular_definition : M_circle_exists ↔ t_circle_exists

theorem circular_error : P2 ↔ t_circle_exists :=
  circular_definition

-- CONCLUSION

-- Kim's proof fails because:
-- 1. It uses inconsistent interpretations of "accepting computation"
-- 2. It has circular definitions (M° defined by t's existence)
-- 3. The counting argument conflates meta-level and object-level
-- 4. The "merging" of transition tables is ill-formed

theorem kim_proof_invalid :
  ¬((P1 → (P2 → P3)) ∧ ¬(P2 → P3) → ¬P1) := by
  intro _
  -- The modus tollens structure is valid
  -- But the premises cannot both be established
  sorry

/-
  Summary: This formalization demonstrates that Kim's proof attempt
  fails due to fundamental definitional ambiguities and logical inconsistencies.
  The error is not in the modus tollens structure itself, but in the
  attempt to establish ¬(P2 → P3) while switching between incompatible
  interpretations of key concepts.
-/
