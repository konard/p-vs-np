/-
  Formalization of Joonmo Kim's 2014 P≠NP Proof Attempt

  This file attempts to formalize the proof from:
  Joonmo Kim. "P is not equal to NP by Modus Tollens."
  arXiv:1403.4143v7 [cs.CC], October 2018.

  The formalization reveals fundamental errors in the proof structure.
-/

/-! ## Basic Complexity Theory Setup -/

-- We model problems, algorithms, and complexity classes abstractly

axiom Problem : Type
axiom Algorithm : Type
axiom TuringMachine : Type
axiom Input : Type
axiom SATInstance : Type
axiom TransitionTable : Type
axiom Computation : Type

-- A complexity class is a set of problems
axiom ComplexityClass : Type
axiom P : ComplexityClass
axiom NP : ComplexityClass

-- Problem membership in complexity classes
axiom in_class : Problem → ComplexityClass → Prop

-- Equality of complexity classes
def P_eq_NP : Prop := ∀ prob, in_class prob P ↔ in_class prob NP
def P_neq_NP : Prop := ¬P_eq_NP

-- SAT is a specific problem
axiom SAT : Problem

-- SAT is NP-complete
axiom SAT_in_NP : in_class SAT NP

/-! ## Cook's Encoding -/

-- Cook's theorem: accepting computations can be encoded as SAT instances
axiom cook_encode : Computation → SATInstance

-- SAT instances have two parts: input part and run part
axiom input_part : SATInstance → SATInstance
axiom run_part : SATInstance → SATInstance

-- Concatenation of SAT instance parts
axiom concat_sat : SATInstance → SATInstance → SATInstance

-- Number of clauses in a SAT instance
axiom num_clauses : SATInstance → Nat

-- SAT satisfiability
axiom satisfiable : SATInstance → Prop

/-! ## Computations and Transition Tables -/

-- A computation is an accepting computation of a TM on some input
axiom is_accepting_computation : TuringMachine → Input → Computation → Prop

-- Number of transitions in a computation
axiom num_transitions : Computation → Nat

-- A transition table can produce a computation
axiom produces_computation : TransitionTable → Computation → Prop

/-! ## Kim's "Particular Transition Table" Concept -/

/-
  Kim introduces "particular transition tables" - transition tables
  "particularly for just one or two accepting problem instances".
  This concept is poorly defined and creates confusion.

  We attempt to model it as: a transition table that can produce
  a specific computation. But note that a standard TM transition
  table is not "particular" to specific inputs - it works for all inputs.
-/

def particular_transition_table_for (t : TransitionTable) (c : Computation) : Prop :=
  produces_computation t c

/-! ## Algorithm M_i -/

/-
  M_i is a Turing machine that:
  - Contains run-parts c^r_1, ..., c^r_n
  - On input y, concatenates c^y with each c^r_ij
  - Checks satisfiability of each concatenation
  - Accepts if an odd number are satisfiable
-/

structure Algorithm_M where
  run_parts : List SATInstance
  sat_solver_module : SATInstance → Bool
  tm_implementation : TuringMachine

/-! ## Algorithm M^o -/

/-
  M^o is defined as an M where:
  - ac_M is the accepting computation of M on input y
  - t is a particular transition table for ac_M
  - c^o is one of the SAT instances appearing during M's run
  - ac_c^o is the accepting computation described by c^o
  - If t is also a particular transition table for ac_c^o, then M is M^o

  PROBLEM: This definition is circular! Whether c^o appears during M's run
  depends on what transition table M uses, which is what we're trying to define.
-/

-- We model M^o abstractly to expose the circularity
axiom Algorithm_M_o : Type
axiom is_M_o : Algorithm_M → Input → Computation → TransitionTable →
               SATInstance → Computation → Prop

/-
  The definition would be:
  is_M_o M y ac_M t c_o ac_c_o :=
    is_accepting_computation (M.tm_implementation) y ac_M ∧
    particular_transition_table_for t ac_M ∧
    (∃ (some condition), c_o appears during M's run) ∧  -- CIRCULAR!
    (ac_c_o is the computation described by c_o) ∧
    particular_transition_table_for t ac_c_o
-/

/-! ## D_sat and ND_sat -/

/-
  D_sat: particular transition table where M^o runs deterministically
  and SAT-solver runs in deterministic polynomial time.

  ND_sat: non-deterministic version.
-/

axiom is_Dsat : TransitionTable → Prop
axiom is_NDsat : TransitionTable → Prop

-- P = NP implies deterministic poly-time SAT solver exists
axiom P_eq_NP_implies_poly_SAT_solver :
  P_eq_NP → ∃ (solver : SATInstance → Bool), True -- simplified

/-! ## The Attempted Proof -/

/-
  The proof attempts to use modus tollens:
  (P1 → (P2 → P3)) ∧ ¬(P2 → P3) implies ¬P1

  Where:
  P1: P = NP
  P2: M^o exists
  P3: there exists t which is D_sat
-/

def P1 := P_eq_NP
def P2 := ∃ (M : Algorithm_M_o), True -- M^o exists
def P3 := ∃ (t : TransitionTable), is_Dsat t

/-! ### Part 1: Attempt to prove P1 → (P2 → P3) -/

/-
  Kim's argument: If P = NP, then there exists a deterministic poly-time
  SAT solver, so M^o can use it, making D_sat exist.

  PROBLEM: This argument is incomplete. The existence of a poly-time SAT solver
  doesn't immediately imply that M^o can be constructed with D_sat property,
  because M^o's definition itself is circular and ill-defined.
-/

theorem part1_attempt : P1 → (P2 → P3) := by
  intro h_P_eq_NP
  intro ⟨M, _⟩
  -- We would need to construct a D_sat transition table
  -- But M^o's definition is circular, so we cannot proceed
  sorry -- Cannot complete - definition of M^o is flawed

/-! ### Part 2: Attempt to prove ¬(P2 → P3) -/

/-
  Kim's argument has two sub-parts:
  a) Show P2 is true (M^o exists via ND_sat)
  b) Show P2 → P3 leads to contradiction
-/

/-
  Sub-part (a): Kim claims M^o exists by constructing ND_sat.

  PROBLEM: The construction assumes we can "merge two non-deterministic
  particular transition tables" in a meaningful way, but this operation
  is not well-defined.
-/

theorem part2a_M_o_exists : P2 := by
  -- We would need to construct M^o using ND_sat
  -- But the construction relies on ill-defined "merging" operation
  sorry -- Cannot complete - construction is ill-defined

/-
  Sub-part (b): Kim claims P2 → P3 leads to contradiction via i > j > k and i = k.

  Let's attempt to formalize the inequalities:
  - i = num_transitions ac_M_o (transitions in M^o's accepting computation)
  - j = num_clauses c_o (clauses in SAT instance c^o)
  - k = num_transitions ac_c_o (transitions in computation described by c^o)
-/

/-
  PROBLEM 1: The claim "i > j" is unjustified.
  Kim argues that "all clauses of c^o should once be loaded on the tape"
  implies i > j. But number of transitions ≠ number of clauses loaded.
  There's no theorem supporting this relationship.
-/

/-
  We cannot prove this because it's simply not true in general:
-/
axiom kim_inequality_i_gt_j :
  ∀ (ac_M_o : Computation) (c_o : SATInstance),
    num_transitions ac_M_o > num_clauses c_o

/-
  This is NOT a theorem. It cannot be proven.
  The number of transitions in a computation and the number of clauses
  in a SAT instance are incommensurable quantities with no such relationship.
-/

/-
  PROBLEM 2: The claim "j > k" is also unjustified.
  Kim cites Cook's theorem that "each transition is described by more than one clauses",
  suggesting k < j. But Cook's encoding goes from computation to SAT, not vice versa.
  The relationship between j (clauses in c^o) and k (transitions in the computation
  that c^o describes) is not what Kim claims.
-/

axiom kim_inequality_j_gt_k :
  ∀ (c_o : SATInstance) (ac_c_o : Computation),
    num_clauses c_o > num_transitions ac_c_o

/-
  This is also NOT generally true.
  Cook's theorem encodes transitions as clauses (transitions → clauses),
  but Kim is trying to use the reverse direction with incorrect logic.
-/

/-
  PROBLEM 3: The claim that ac_M_o and ac_c_o are "exactly the same computation"
  if they share a D_sat table and same input is a non-sequitur.

  ac_M_o is M^o's accepting computation on input y.
  ac_c_o is the computation encoded by SAT instance c^o.

  These are fundamentally different computations! There's no reason they'd be identical.
-/

axiom kim_same_computation_claim :
  ∀ (M_o : Algorithm_M_o) (y : Input) (ac_M_o ac_c_o : Computation)
    (t : TransitionTable),
    is_Dsat t →
    particular_transition_table_for t ac_M_o →
    particular_transition_table_for t ac_c_o →
    -- same input condition →
    ac_M_o = ac_c_o

/-
  This is FALSE. Different computations can share properties without being identical.
-/

/-
  The supposed contradiction i > j > k and i = k cannot be established
  because the inequalities are not theorems.
-/

theorem part2b_contradiction : (P2 → P3) → False := by
  intro h
  -- We would need to establish:
  -- 1. If P2 → P3, then ac_M_o and ac_c_o are the same
  -- 2. i > j > k (where i, j, k are as defined above)
  -- 3. i = k (from ac_M_o and ac_c_o being the same)
  -- 4. Derive contradiction from i > k and i = k
  --
  -- But steps 1 and 2 cannot be proven because they're not valid.
  sorry -- Cannot complete - the inequalities are not theorems

/-! ### The Failed Modus Tollens -/

/-
  Even if we admitted all the above flawed lemmas, the modus tollens would be:
-/

theorem kim_attempted_proof : P_neq_NP := by
  unfold P_neq_NP
  intro h_P_eq_NP

  -- Modus tollens structure: (P1 → (P2 → P3)) ∧ ¬(P2 → P3) implies ¬P1
  -- We need to show: P_eq_NP → False

  -- This would require part1_attempt and part2b_contradiction
  -- But both are flawed as shown above

  sorry -- Cannot complete - the proof structure is fundamentally flawed

/-! ## Formalization Conclusion -/

/-
  This formalization attempt reveals the following errors in Kim's proof:

  1. The definition of M^o is circular and cannot be formalized
  2. The concept of "particular transition table" is ill-defined
  3. The inequalities i > j and j > k are not theorems and cannot be proven
  4. The claim that ac_M_o = ac_c_o under the stated conditions is false
  5. The modus tollens structure fails because its premises are not established

  The proof cannot be completed in any rigorous formal system, demonstrating
  that it is fundamentally flawed rather than merely having minor gaps.
-/

/-! ## Educational Value -/

/-
  This formalization exercise demonstrates the power of formal verification
  in identifying subtle (and not-so-subtle) errors in mathematical arguments.

  Key lessons:
  - Definitions must be non-circular and well-founded
  - Quantitative relationships between different entities need rigorous justification
  - Informal arguments that "seem reasonable" often hide unjustified assumptions
  - Formal proof assistants force us to make all assumptions explicit
-/
