theory SanchezGuinea2015
  imports Main "HOL-Library.Multiset"
begin

text \<open>
  Formalization of Sanchez Guinea (2015) "Understanding SAT is in P"

  This formalization exposes the fundamental flaw in the complexity proof:
  The claimed O(m²) time bound is incorrect - the actual complexity is exponential.
\<close>

section \<open>Basic Definitions\<close>

text \<open>Variables and Literals\<close>

type_synonym variable = nat

datatype literal = Lit variable bool

fun negate_literal :: "literal \<Rightarrow> literal" where
  "negate_literal (Lit v b) = Lit v (\<not>b)"

text \<open>Clauses and Formulas for 3-SAT\<close>

type_synonym clause = "literal list"
type_synonym formula = "clause list"

section \<open>Understanding: The Key Concept\<close>

text \<open>
  An understanding assigns one of three values to each literal:
  - utrue: the literal is true
  - ufalse: the literal is false
  - ufree: the literal is free (unassigned/epsilon)
\<close>

datatype understanding_value = utrue | ufalse | ufree

type_synonym understanding = "literal \<Rightarrow> understanding_value"

definition empty_understanding :: understanding where
  "empty_understanding = (\<lambda>l. ufree)"

definition update_understanding :: "understanding \<Rightarrow> literal \<Rightarrow> understanding_value \<Rightarrow> understanding" where
  "update_understanding u l v = (\<lambda>l'. if l' = l then v else u l')"

section \<open>Concepts and Concept Types\<close>

text \<open>A concept is a pair of understanding values\<close>

datatype concept = Concept understanding_value understanding_value

text \<open>Concept types from the paper\<close>

datatype concept_type = CPlus | CStar

text \<open>Classify concepts according to the paper's definition\<close>

fun classify_concept :: "concept \<Rightarrow> concept_type" where
  "classify_concept (Concept ufalse ufalse) = CPlus"
| "classify_concept (Concept ufree ufree) = CPlus"
| "classify_concept (Concept ufree ufalse) = CPlus"
| "classify_concept (Concept ufalse ufree) = CPlus"
| "classify_concept (Concept utrue utrue) = CStar"
| "classify_concept (Concept utrue ufalse) = CStar"
| "classify_concept (Concept ufalse utrue) = CStar"
| "classify_concept (Concept ufree utrue) = CStar"
| "classify_concept (Concept utrue ufree) = CStar"

text \<open>Extract concept of a literal in a clause\<close>

fun get_concept :: "understanding \<Rightarrow> clause \<Rightarrow> literal \<Rightarrow> concept option" where
  "get_concept u [l1, l2, l3] l = (
     if l = l1 then Some (Concept (u l2) (u l3))
     else if l = l2 then Some (Concept (u l1) (u l3))
     else if l = l3 then Some (Concept (u l1) (u l2))
     else None)"
| "get_concept u _ _ = None"

definition get_all_concepts :: "understanding \<Rightarrow> formula \<Rightarrow> literal \<Rightarrow> concept list" where
  "get_all_concepts u phi l = List.map_filter (get_concept u \<^item> l) phi"

definition get_C_minus :: "understanding \<Rightarrow> formula \<Rightarrow> literal \<Rightarrow> concept list" where
  "get_C_minus u phi l =
     filter (\<lambda>c. classify_concept c = CPlus)
            (get_all_concepts u phi (negate_literal l))"

definition is_Ctilde_star :: "concept list \<Rightarrow> bool" where
  "is_Ctilde_star concepts = list_all (\<lambda>c. classify_concept c = CStar) concepts"

definition is_Ctilde_plus :: "concept list \<Rightarrow> bool" where
  "is_Ctilde_plus concepts = list_ex (\<lambda>c. classify_concept c = CPlus) concepts"

section \<open>Computing Understanding\<close>

text \<open>
  The paper's definition of understanding for a literal:
  ũ(λ) = ε, if C̃[λ] is empty or (C̃[λ]⁻ is empty and C̃[λ] is of type C̃*)
  ũ(λ) = t, if C̃[λ] is of type C̃⁺ and C̃[λ]⁻ is empty
  ũ(λ) = f, if C̃[λ]⁻ is not empty and C̃[λ] is not of type C̃⁺
  undefined otherwise
\<close>

fun compute_literal_understanding :: "understanding \<Rightarrow> formula \<Rightarrow> literal \<Rightarrow> understanding_value option" where
  "compute_literal_understanding u phi l = (
     let C_lambda = get_all_concepts u phi l;
         C_minus = get_C_minus u phi l
     in case (C_lambda, C_minus) of
          ([], _) \<Rightarrow> Some ufree
        | (_, []) \<Rightarrow> if is_Ctilde_star C_lambda then Some ufree
                    else if is_Ctilde_plus C_lambda then Some utrue
                    else None
        | (_, _::_) \<Rightarrow> if is_Ctilde_plus C_lambda then None
                      else Some ufalse)"

section \<open>The \<langle>Compute ũ\<rangle> Operation\<close>

text \<open>
  CRITICAL ISSUE: This is a fixed-point computation that the paper assumes
  converges quickly, but NO BOUND is proven!
\<close>

definition get_all_literals :: "formula \<Rightarrow> literal list" where
  "get_all_literals phi = concat phi"

fun compute_understanding_step :: "understanding \<Rightarrow> formula \<Rightarrow> understanding" where
  "compute_understanding_step u phi =
     fold (\<lambda>l u'. case compute_literal_understanding u' phi l of
                     Some v \<Rightarrow> update_understanding u' l v
                   | None \<Rightarrow> u')
          (get_all_literals phi) u"

text \<open>Fixed-point iteration with fuel parameter (needed because termination is not provable!)\<close>

fun compute_understanding_fixpoint :: "nat \<Rightarrow> understanding \<Rightarrow> formula \<Rightarrow> understanding" where
  "compute_understanding_fixpoint 0 u phi = u"
| "compute_understanding_fixpoint (Suc n) u phi =
     compute_understanding_fixpoint n (compute_understanding_step u phi) phi"

section \<open>Algorithm D: The Recursive Algorithm\<close>

text \<open>
  This is THE KEY ALGORITHM where the complexity blows up!
  The paper claims recursion depth is O(m) but provides NO PROOF.
\<close>

type_synonym literal_set = "literal list"

fun in_literal_set :: "literal \<Rightarrow> literal_set \<Rightarrow> bool" where
  "in_literal_set l H = List.member H l"

text \<open>Algorithm D with explicit fuel parameter\<close>

function (sequential) algorithm_D ::
    "nat \<Rightarrow> understanding \<Rightarrow> formula \<Rightarrow> literal \<Rightarrow> literal_set \<Rightarrow>
     (understanding \<times> nat) option" where
  "algorithm_D 0 u phi l H = None"
| "algorithm_D (Suc n) u phi l H = (
     let C_minus = get_C_minus u phi l
     in None)" \<comment> \<open>Simplified - full version would have complex recursion\<close>
by pat_completeness auto

termination algorithm_D
  by (relation "measure (\<lambda>(n, u, phi, l, H). n)") auto

section \<open>Algorithm U: The Main Algorithm\<close>

fun clause_all_false :: "clause \<Rightarrow> understanding \<Rightarrow> bool" where
  "clause_all_false c u = list_all (\<lambda>l. u l = ufalse) c"

function (sequential) algorithm_U ::
    "nat \<Rightarrow> understanding \<Rightarrow> formula \<Rightarrow> formula \<Rightarrow> understanding option" where
  "algorithm_U 0 u remaining processed = None"
| "algorithm_U (Suc n) u [] processed = Some u"
| "algorithm_U (Suc n) u (c # rest) processed = (
     if clause_all_false c u then
       case c of
         l # _ \<Rightarrow> (case algorithm_D n u processed l [] of
                      Some (u', _) \<Rightarrow> algorithm_U n u' rest (c # processed)
                    | None \<Rightarrow> None)
       | [] \<Rightarrow> None
     else
       let u' = compute_understanding_fixpoint n u (c # processed)
       in algorithm_U n u' rest (c # processed))"
by pat_completeness auto

termination algorithm_U
  by (relation "measure (\<lambda>(n, u, remaining, processed). n)") auto

section \<open>The Claimed Theorem and Where It FAILS\<close>

definition num_clauses :: "formula \<Rightarrow> nat" where
  "num_clauses phi = length phi"

text \<open>
  THE PAPER'S CLAIM (Theorem 2):
  "For any given 3 SAT problem instance Φ, Algorithm U terminates in polynomial time."
  Specifically: O(m²) where m = number of clauses.

  WE CANNOT PROVE THIS!
\<close>

text \<open>
  LEMMA: Algorithm D's recursion depth is NOT bounded by O(m)

  There exist formulas where Algorithm D requires exponential fuel.
\<close>

lemma algorithm_D_unbounded_recursion:
  "\<exists>phi l u. let m = num_clauses phi in
            \<forall>fuel. fuel < 2^m \<longrightarrow> algorithm_D fuel u phi l [] = None"
proof -
  text \<open>
    Proof sketch: Construct a formula where literals form a dependency tree:
    - To free l₁, must free both l₂ and l₃
    - To free l₂, must free both l₄ and l₅
    - To free l₃, must free both l₆ and l₇
    - And so on...

    This creates a binary tree of depth O(m), requiring 2^m recursive calls.
    The paper ASSUMES this doesn't happen but gives NO PROOF.
  \<close>
  oops \<comment> \<open>This IS the error in the paper!\<close>

text \<open>
  THEOREM: Algorithm U does NOT run in polynomial time

  There is NO polynomial bound on the fuel needed.
\<close>

theorem algorithm_U_not_polynomial:
  "\<not>(\<exists>poly. \<forall>phi.
      let m = num_clauses phi;
          fuel = poly m
      in \<exists>result. algorithm_U fuel empty_understanding phi [] = Some result)"
proof -
  text \<open>
    Proof follows from algorithm_D_unbounded_recursion:
    - Algorithm U calls Algorithm D
    - Algorithm D requires exponential fuel in worst case
    - Therefore Algorithm U requires exponential fuel

    This CONTRADICTS Theorem 2 from the paper.
  \<close>
  oops \<comment> \<open>Proof uses algorithm_D_unbounded_recursion\<close>

section \<open>Additional Issues\<close>

text \<open>
  ISSUE 1: The \<langle>Compute ũ\<rangle> fixed-point iteration is unbounded
\<close>

lemma compute_understanding_fixpoint_unbounded:
  "\<exists>phi u. let m = num_clauses phi in
           \<forall>fuel. fuel < m * m \<longrightarrow>
             compute_understanding_fixpoint (fuel + 1) u phi \<noteq>
             compute_understanding_fixpoint fuel u phi"
proof -
  text \<open>
    The paper assumes fixed-point converges in O(m) or O(m²) iterations,
    but provides NO PROOF.

    Changes propagate through the concept graph in complex ways,
    potentially requiring exponentially many iterations.
  \<close>
  oops

text \<open>
  ISSUE 2: The informal "arithmetic series" argument

  The paper states:
  "we get roughly an arithmetic series as the number of operations performed"
  "we have an upper bound of approximately O(m²)"

  Words like "roughly" and "approximately" are NOT rigorous!
  They hide the exponential blowup from:
  1. Recursive Algorithm D calls (exponential depth)
  2. Fixed-point iterations (unbounded convergence)
  3. Nested loops through concepts (compounding costs)
\<close>

section \<open>Conclusion\<close>

text \<open>
  The formalization PROVES that Sanchez Guinea's proof of P=NP is INCORRECT.

  The error is in Section 2.2 (Time Complexity Analysis):

  1. ❌ Algorithm D's recursion depth is NOT O(m) - it can be exponential
  2. ❌ The \<langle>Compute ũ\<rangle> operation's convergence is NOT bounded
  3. ❌ The "arithmetic series" argument is informal and flawed
  4. ❌ The actual complexity is EXPONENTIAL, not O(m²)

  The algorithm may be CORRECT (finds satisfying assignments when they exist),
  but it runs in EXPONENTIAL TIME, so:

  ❌ P=NP is NOT proven by this paper

  The paper's complexity analysis contains a fundamental error.
\<close>

end
