(*
  Formalization of Joonmo Kim's 2014 P≠NP Proof Attempt

  This file attempts to formalize the proof from:
  Joonmo Kim. "P is not equal to NP by Modus Tollens."
  arXiv:1403.4143v7 [cs.CC], October 2018.

  The formalization reveals fundamental errors in the proof structure.
*)

theory JoonmoKim2014
  imports Main
begin

section \<open>Basic Complexity Theory Setup\<close>

text \<open>We model problems, algorithms, and complexity classes abstractly\<close>

typedecl Problem
typedecl Algorithm
typedecl TuringMachine
typedecl Input
typedecl SATInstance
typedecl TransitionTable
typedecl Computation

text \<open>A complexity class is a set of problems\<close>
typedecl ComplexityClass

consts
  P :: ComplexityClass
  NP :: ComplexityClass

text \<open>Problem membership in complexity classes\<close>
consts in_class :: "Problem \<Rightarrow> ComplexityClass \<Rightarrow> bool"

text \<open>Equality of complexity classes\<close>
definition P_eq_NP :: bool where
  "P_eq_NP \<equiv> (\<forall>prob. in_class prob P \<longleftrightarrow> in_class prob NP)"

definition P_neq_NP :: bool where
  "P_neq_NP \<equiv> \<not> P_eq_NP"

text \<open>SAT is a specific problem\<close>
consts SAT :: Problem

text \<open>SAT is NP-complete\<close>
axiomatization where
  SAT_in_NP: "in_class SAT NP"

section \<open>Cook's Encoding\<close>

text \<open>Cook's theorem: accepting computations can be encoded as SAT instances\<close>
consts cook_encode :: "Computation \<Rightarrow> SATInstance"

text \<open>SAT instances have two parts: input part and run part\<close>
consts
  input_part :: "SATInstance \<Rightarrow> SATInstance"
  run_part :: "SATInstance \<Rightarrow> SATInstance"

text \<open>Concatenation of SAT instance parts\<close>
consts concat_sat :: "SATInstance \<Rightarrow> SATInstance \<Rightarrow> SATInstance"

text \<open>Number of clauses in a SAT instance\<close>
consts num_clauses :: "SATInstance \<Rightarrow> nat"

text \<open>SAT satisfiability\<close>
consts satisfiable :: "SATInstance \<Rightarrow> bool"

section \<open>Computations and Transition Tables\<close>

text \<open>A computation is an accepting computation of a TM on some input\<close>
consts is_accepting_computation :: "TuringMachine \<Rightarrow> Input \<Rightarrow> Computation \<Rightarrow> bool"

text \<open>Number of transitions in a computation\<close>
consts num_transitions :: "Computation \<Rightarrow> nat"

text \<open>A transition table can produce a computation\<close>
consts produces_computation :: "TransitionTable \<Rightarrow> Computation \<Rightarrow> bool"

section \<open>Kim's "Particular Transition Table" Concept\<close>

text \<open>
  Kim introduces "particular transition tables" - transition tables
  "particularly for just one or two accepting problem instances".
  This concept is poorly defined and creates confusion.

  We attempt to model it as: a transition table that can produce
  a specific computation. But note that a standard TM transition
  table is not "particular" to specific inputs - it works for all inputs.
\<close>

definition particular_transition_table_for :: "TransitionTable \<Rightarrow> Computation \<Rightarrow> bool" where
  "particular_transition_table_for t c \<equiv> produces_computation t c"

section \<open>Algorithm M\<^sub>i\<close>

text \<open>
  M\<^sub>i is a Turing machine that:
  - Contains run-parts c\<^sup>r\<^sub>1, ..., c\<^sup>r\<^sub>n
  - On input y, concatenates c\<^sup>y with each c\<^sup>r\<^sub>i\<^sub>j
  - Checks satisfiability of each concatenation
  - Accepts if an odd number are satisfiable
\<close>

record Algorithm_M =
  run_parts :: "SATInstance list"
  sat_solver_module :: "SATInstance \<Rightarrow> bool"
  tm_implementation :: TuringMachine

section \<open>Algorithm M\<^sup>o\<close>

text \<open>
  M\<^sup>o is defined as an M where:
  - ac\<^sub>M is the accepting computation of M on input y
  - t is a particular transition table for ac\<^sub>M
  - c\<^sup>o is one of the SAT instances appearing during M's run
  - ac\<^sub>c\<^sup>o is the accepting computation described by c\<^sup>o
  - If t is also a particular transition table for ac\<^sub>c\<^sup>o, then M is M\<^sup>o

  PROBLEM: This definition is circular! Whether c\<^sup>o appears during M's run
  depends on what transition table M uses, which is what we're trying to define.
\<close>

typedecl Algorithm_M_o

consts is_M_o :: "Algorithm_M \<Rightarrow> Input \<Rightarrow> Computation \<Rightarrow> TransitionTable \<Rightarrow>
                   SATInstance \<Rightarrow> Computation \<Rightarrow> bool"

text \<open>
  The definition would be:
  is_M_o M y ac_M t c_o ac_c_o \<equiv>
    is_accepting_computation (tm_implementation M) y ac_M \<and>
    particular_transition_table_for t ac_M \<and>
    (\<exists>some_condition. c_o appears during M's run) \<and>  (* CIRCULAR! *)
    (ac_c_o is the computation described by c_o) \<and>
    particular_transition_table_for t ac_c_o
\<close>

section \<open>D\<^sub>sat and ND\<^sub>sat\<close>

text \<open>
  D\<^sub>sat: particular transition table where M\<^sup>o runs deterministically
  and SAT-solver runs in deterministic polynomial time.

  ND\<^sub>sat: non-deterministic version.
\<close>

consts
  is_Dsat :: "TransitionTable \<Rightarrow> bool"
  is_NDsat :: "TransitionTable \<Rightarrow> bool"

text \<open>P = NP implies deterministic poly-time SAT solver exists\<close>
axiomatization where
  P_eq_NP_implies_poly_SAT_solver: "P_eq_NP \<longrightarrow> (\<exists>solver. True)"

section \<open>The Attempted Proof\<close>

text \<open>
  The proof attempts to use modus tollens:
  (P1 \<longrightarrow> (P2 \<longrightarrow> P3)) \<and> \<not>(P2 \<longrightarrow> P3) implies \<not>P1

  Where:
  P1: P = NP
  P2: M\<^sup>o exists
  P3: there exists t which is D\<^sub>sat
\<close>

definition P1 :: bool where "P1 \<equiv> P_eq_NP"
definition P2 :: bool where "P2 \<equiv> (\<exists>M. True)" (* M\<^sup>o exists *)
definition P3 :: bool where "P3 \<equiv> (\<exists>t. is_Dsat t)"

subsection \<open>Part 1: Attempt to prove P1 \<longrightarrow> (P2 \<longrightarrow> P3)\<close>

text \<open>
  Kim's argument: If P = NP, then there exists a deterministic poly-time
  SAT solver, so M\<^sup>o can use it, making D\<^sub>sat exist.

  PROBLEM: This argument is incomplete. The existence of a poly-time SAT solver
  doesn't immediately imply that M\<^sup>o can be constructed with D\<^sub>sat property,
  because M\<^sup>o's definition itself is circular and ill-defined.
\<close>

lemma part1_attempt: "P1 \<longrightarrow> (P2 \<longrightarrow> P3)"
  oops (* Cannot complete - definition of M\<^sup>o is flawed *)

subsection \<open>Part 2: Attempt to prove \<not>(P2 \<longrightarrow> P3)\<close>

text \<open>
  Kim's argument has two sub-parts:
  a) Show P2 is true (M\<^sup>o exists via ND\<^sub>sat)
  b) Show P2 \<longrightarrow> P3 leads to contradiction
\<close>

text \<open>
  Sub-part (a): Kim claims M\<^sup>o exists by constructing ND\<^sub>sat.

  PROBLEM: The construction assumes we can "merge two non-deterministic
  particular transition tables" in a meaningful way, but this operation
  is not well-defined.
\<close>

lemma part2a_M_o_exists: "P2"
  oops (* Cannot complete - construction is ill-defined *)

text \<open>
  Sub-part (b): Kim claims P2 \<longrightarrow> P3 leads to contradiction via i > j > k and i = k.

  Let's attempt to formalize the inequalities:
  - i = num_transitions ac_M_o (transitions in M\<^sup>o's accepting computation)
  - j = num_clauses c_o (clauses in SAT instance c\<^sup>o)
  - k = num_transitions ac_c_o (transitions in computation described by c\<^sup>o)
\<close>

text \<open>
  PROBLEM 1: The claim "i > j" is unjustified.
  Kim argues that "all clauses of c\<^sup>o should once be loaded on the tape"
  implies i > j. But number of transitions \<noteq> number of clauses loaded.
  There's no theorem supporting this relationship.
\<close>

text \<open>
  We cannot prove this because it's simply not true in general:

  This is NOT a theorem. It cannot be proven.
  The number of transitions in a computation and the number of clauses
  in a SAT instance are incommensurable quantities with no such relationship.
\<close>

axiomatization where
  kim_inequality_i_gt_j: "\<forall>ac_M_o c_o. num_transitions ac_M_o > num_clauses c_o"

text \<open>
  PROBLEM 2: The claim "j > k" is also unjustified.
  Kim cites Cook's theorem that "each transition is described by more than one clauses",
  suggesting k < j. But Cook's encoding goes from computation to SAT, not vice versa.
  The relationship between j (clauses in c\<^sup>o) and k (transitions in the computation
  that c\<^sup>o describes) is not what Kim claims.
\<close>

axiomatization where
  kim_inequality_j_gt_k: "\<forall>c_o ac_c_o. num_clauses c_o > num_transitions ac_c_o"

text \<open>
  This is also NOT generally true.
  Cook's theorem encodes transitions as clauses (transitions \<rightarrow> clauses),
  but Kim is trying to use the reverse direction with incorrect logic.
\<close>

text \<open>
  PROBLEM 3: The claim that ac_M_o and ac_c_o are "exactly the same computation"
  if they share a D\<^sub>sat table and same input is a non-sequitur.

  ac_M_o is M\<^sup>o's accepting computation on input y.
  ac_c_o is the computation encoded by SAT instance c\<^sup>o.

  These are fundamentally different computations! There's no reason they'd be identical.

  This is FALSE. Different computations can share properties without being identical.
\<close>

axiomatization where
  kim_same_computation_claim:
    "\<forall>M_o y ac_M_o ac_c_o t.
       is_Dsat t \<longrightarrow>
       particular_transition_table_for t ac_M_o \<longrightarrow>
       particular_transition_table_for t ac_c_o \<longrightarrow>
       ac_M_o = ac_c_o"

text \<open>
  The supposed contradiction i > j > k and i = k cannot be established
  because the inequalities are not theorems.
\<close>

lemma part2b_contradiction: "(P2 \<longrightarrow> P3) \<longrightarrow> False"
  oops (* Cannot complete - the inequalities are not theorems *)

subsection \<open>The Failed Modus Tollens\<close>

text \<open>Even if we admitted all the above flawed lemmas, the modus tollens would be:\<close>

theorem kim_attempted_proof: "P_neq_NP"
  oops (* Cannot complete - the proof structure is fundamentally flawed *)

section \<open>Formalization Conclusion\<close>

text \<open>
  This formalization attempt reveals the following errors in Kim's proof:

  1. The definition of M\<^sup>o is circular and cannot be formalized
  2. The concept of "particular transition table" is ill-defined
  3. The inequalities i > j and j > k are not theorems and cannot be proven
  4. The claim that ac_M_o = ac_c_o under the stated conditions is false
  5. The modus tollens structure fails because its premises are not established

  The proof cannot be completed in any rigorous formal system, demonstrating
  that it is fundamentally flawed rather than merely having minor gaps.
\<close>

section \<open>Educational Value\<close>

text \<open>
  This formalization exercise demonstrates the power of formal verification
  in identifying subtle (and not-so-subtle) errors in mathematical arguments.

  Key lessons:
  - Definitions must be non-circular and well-founded
  - Quantitative relationships between different entities need rigorous justification
  - Informal arguments that "seem reasonable" often hide unjustified assumptions
  - Formal proof assistants force us to make all assumptions explicit
\<close>

end
