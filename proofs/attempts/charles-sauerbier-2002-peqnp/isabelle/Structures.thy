theory Structures
  imports Main
begin

section \<open>Charles Sauerbier (2002) - Core Structures\<close>

text \<open>
This theory formalizes the C/DNF and C/CNF structures used in Sauerbier's
polynomial-time 3SAT algorithms.

Reference: arXiv:cs/0205064v3
\<close>

subsection \<open>Basic Definitions\<close>

text \<open>Boolean variables are represented as natural numbers\<close>
type_synonym Var = nat

text \<open>A literal is a variable with a polarity (True = positive, False = negative)\<close>
type_synonym Literal = "Var \<times> bool"

text \<open>A clause is a list of literals\<close>
type_synonym Clause = "Literal list"

text \<open>A 3SAT clause has exactly 3 literals\<close>
definition is_3SAT_clause :: "Clause \<Rightarrow> bool" where
  "is_3SAT_clause c \<equiv> length c = 3"

text \<open>A CNF expression is a list of clauses\<close>
type_synonym CNF = "Clause list"

text \<open>A 3SAT expression has only 3-clauses\<close>
definition is_3SAT :: "CNF \<Rightarrow> bool" where
  "is_3SAT cnf \<equiv> \<forall>c \<in> set cnf. is_3SAT_clause c"

subsection \<open>Assignment Representation\<close>

text \<open>
An assignment to n variables can be represented as a binary string
of length n, or equivalently as a natural number < 2^n.

For 3 variables, we have 8 possible assignments: 000, 001, 010, ..., 111
represented as numbers 0-7.
\<close>

text \<open>Check if a specific bit is set in a number\<close>
definition bit_set :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bit_set a i \<equiv> odd (a div (2 ^ i))"

subsection \<open>Byte Representation\<close>

text \<open>
For 3-variable subsets, assignments can be represented using a single byte
where each bit represents one of the 8 possible assignments.

A byte is represented as a natural number < 256.
\<close>

type_synonym Byte = nat

text \<open>The zero byte (00000000) represents empty set of assignments\<close>
definition zero_byte :: Byte where
  "zero_byte = 0"

text \<open>The full byte (11111111) represents all assignments\<close>
definition full_byte :: Byte where
  "full_byte = 255"

text \<open>Check if a byte is zero (no assignments)\<close>
definition is_zero_byte :: "Byte \<Rightarrow> bool" where
  "is_zero_byte b \<equiv> b = 0"

text \<open>Check if a byte is full (all assignments/constraints)\<close>
definition is_full_byte :: "Byte \<Rightarrow> bool" where
  "is_full_byte b \<equiv> b = 255"

text \<open>Valid byte constraint\<close>
definition valid_byte :: "Byte \<Rightarrow> bool" where
  "valid_byte b \<equiv> b < 256"

text \<open>Set a bit in a byte (add an assignment/constraint)\<close>
(* NOTE: Isabelle's bitwise operations require specific imports.
   We provide simplified definitions that avoid bitwise operators. *)
definition set_bit_byte :: "Byte \<Rightarrow> nat \<Rightarrow> Byte" where
  "set_bit_byte b i = (if bit_set b i then b else (b + 2 ^ i) mod 256)"

text \<open>Clear a bit in a byte (remove an assignment)\<close>
definition clear_bit_byte :: "Byte \<Rightarrow> nat \<Rightarrow> Byte" where
  "clear_bit_byte b i = (if bit_set b i then (b - 2 ^ i) mod 256 else b)"

subsection \<open>Variable Subsets\<close>

text \<open>
P is the set of all 3-variable subsets from the variable set V.

A 3-variable subset is an ordered triple of distinct variables.
\<close>

record VarTriple =
  v1 :: Var
  v2 :: Var
  v3 :: Var

definition valid_var_triple :: "VarTriple \<Rightarrow> bool" where
  "valid_var_triple t \<equiv>
    v1 t \<noteq> v2 t \<and> v1 t \<noteq> v3 t \<and> v2 t \<noteq> v3 t"

subsection \<open>Structure D (C/CNF - Constraint Representation)\<close>

text \<open>
Each element of D is a pair (p, m) where:
- p is a 3-variable subset
- m is a byte representing constraints (clauses) on those variables
\<close>

record D_element =
  d_vars :: VarTriple
  d_constraints :: Byte

text \<open>Structure D is a list of D_elements, one for each 3-variable subset\<close>
type_synonym Structure_D = "D_element list"

text \<open>Initial D structure with no constraints\<close>
definition init_D :: "VarTriple list \<Rightarrow> Structure_D" where
  "init_D vars = map (\<lambda>p. \<lparr>d_vars = p, d_constraints = zero_byte\<rparr>) vars"

subsection \<open>Structure A (C/DNF - Assignment Representation)\<close>

text \<open>
Each element of A is a pair (p, q) where:
- p is a 3-variable subset
- q is a byte representing admitted assignments to those variables
\<close>

record A_element =
  a_vars :: VarTriple
  a_assignments :: Byte

text \<open>Structure A is a list of A_elements, one for each 3-variable subset\<close>
type_synonym Structure_A = "A_element list"

text \<open>Initial A structure with all assignments\<close>
definition init_A :: "VarTriple list \<Rightarrow> Structure_A" where
  "init_A vars = map (\<lambda>p. \<lparr>a_vars = p, a_assignments = full_byte\<rparr>) vars"

subsection \<open>Transformation between D and A\<close>

text \<open>
The key insight: D and A are duals. An assignment in A corresponds to
the absence of a constraint in D, and vice versa.

If A has assignment '100' (bit 4 set), then D should NOT have constraint
'100' (bit 4 clear). The binary string representations are negations.
\<close>

text \<open>Negate a byte (flip all bits in range 0-7)\<close>
(* NOTE: XOR with 255 is equivalent to 255 - b for bytes in range 0-255 *)
definition negate_byte :: "Byte \<Rightarrow> Byte" where
  "negate_byte b = (255 - b)"

text \<open>Transform D element to A element\<close>
definition d_to_a :: "D_element \<Rightarrow> A_element" where
  "d_to_a d = \<lparr>a_vars = d_vars d, a_assignments = negate_byte (d_constraints d)\<rparr>"

text \<open>Transform A element to D element\<close>
definition a_to_d :: "A_element \<Rightarrow> D_element" where
  "a_to_d a = \<lparr>d_vars = a_vars a, d_constraints = negate_byte (a_assignments a)\<rparr>"

subsection \<open>Certificate of Satisfiability/Non-Satisfiability\<close>

text \<open>Certificate of non-satisfiability: some element has empty assignments\<close>
definition is_unsat_certificate_A :: "Structure_A \<Rightarrow> bool" where
  "is_unsat_certificate_A a \<equiv> \<exists>elem \<in> set a. is_zero_byte (a_assignments elem)"

text \<open>Certificate of non-satisfiability: some element has all constraints\<close>
definition is_unsat_certificate_D :: "Structure_D \<Rightarrow> bool" where
  "is_unsat_certificate_D d \<equiv> \<exists>elem \<in> set d. is_full_byte (d_constraints elem)"

text \<open>Certificate of satisfiability: no element is empty\<close>
definition is_sat_certificate_A :: "Structure_A \<Rightarrow> bool" where
  "is_sat_certificate_A a \<equiv> \<forall>elem \<in> set a. \<not> is_zero_byte (a_assignments elem)"

text \<open>Certificate of satisfiability: no element is full\<close>
definition is_sat_certificate_D :: "Structure_D \<Rightarrow> bool" where
  "is_sat_certificate_D d \<equiv> \<forall>elem \<in> set d. \<not> is_full_byte (d_constraints elem)"

subsection \<open>Notes on the Error\<close>

text \<open>
The key problem in Sauerbier's original algorithm was that it only
operated on the SUBSET of D/A elements corresponding to variables
that appear in clauses of the CNF expression.

The corrected version must operate on ALL 3-variable subsets, which
significantly increases the complexity and potentially undermines the
polynomial-time claim.
\<close>

end
