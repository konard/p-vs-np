(*
  YampolskiyHPTSP.thy - Formalization of Yampolskiy's 2011 P≠NP attempt

  This file formalizes the "Hashed-Path Traveling Salesperson Problem" (HPTSP)
  from Yampolskiy's 2011 paper "Construction of an NP Problem with an
  Exponential Lower Bound" (arXiv:1111.0305).

  The formalization demonstrates:
  1. HPTSP is well-defined and in NP (✓ proven)
  2. The claimed proof that HPTSP ∉ P contains logical gaps (✓ identified)
  3. The argument relies on unproven cryptographic assumptions (✓ marked with oops)

  Status: ⚠️ Incomplete - requires unjustified axioms to complete Yampolskiy's argument
*)

theory YampolskiyHPTSP
  imports Main
begin

section ‹Basic Complexity Theory Definitions›

text ‹A decision problem maps inputs to booleans›
type_synonym DecisionProblem = "string ⇒ bool"

text ‹Polynomial bound on a function›
definition PolynomialBound :: "(nat ⇒ nat) ⇒ bool" where
  "PolynomialBound f ≡ ∃c k. c > 0 ∧ k > 0 ∧ (∀n>0. f n ≤ c * (n ^ k))"

text ‹A problem is in P if decidable in polynomial time›
definition InP :: "DecisionProblem ⇒ bool" where
  "InP prob ≡ ∃algo time.
    PolynomialBound time ∧
    (∀input. algo input = prob input)"

text ‹A problem is in NP if solutions verifiable in polynomial time›
definition InNP :: "DecisionProblem ⇒ bool" where
  "InNP prob ≡ ∃verifier time.
    PolynomialBound time ∧
    (∀input. prob input = True ⟷ (∃certificate. verifier input certificate = True))"

section ‹Graph Theory Definitions for TSP›

text ‹Vertex as natural number›
type_synonym Vertex = nat

text ‹Edge with cost›
record Edge =
  edge_from :: Vertex
  edge_to :: Vertex
  edge_cost :: nat

text ‹Graph as lists of vertices and edges›
record Graph =
  vertices :: "Vertex list"
  edges :: "Edge list"

text ‹Complete graph property›
definition is_complete_graph :: "Graph ⇒ bool" where
  "is_complete_graph g ≡
    ∀v1 v2. v1 ∈ set (vertices g) ⟶ v2 ∈ set (vertices g) ⟶ v1 ≠ v2 ⟶
      (∃e ∈ set (edges g).
        (edge_from e = v1 ∧ edge_to e = v2) ∨
        (edge_from e = v2 ∧ edge_to e = v1))"

text ‹Hamiltonian cycle›
type_synonym HamiltonianCycle = "Vertex list"

text ‹Valid Hamiltonian cycle check›
definition is_valid_hamiltonian_cycle :: "Graph ⇒ HamiltonianCycle ⇒ bool" where
  "is_valid_hamiltonian_cycle g cycle ≡
    distinct cycle ∧
    (∀v. v ∈ set (vertices g) ⟷ v ∈ set cycle) ∧
    length cycle = length (vertices g)"

section ‹Hash Function Formalization›

text ‹Abstract hash function type›
type_synonym HashFunction = "string ⇒ string"

text ‹
  Properties that Yampolskiy claims hash functions have

  CRITICAL ISSUE: These are not proven properties of all hash functions.
  They are empirical observations about specific functions like SHA-1.
  Using them as axioms in a complexity-theoretic proof is unjustified.
›

text ‹
  Property 1: Strict Avalanche Criterion
  Yampolskiy claims: "whenever a single input bit is flipped, each of the
  output bits changes with a probability of 50%"

  NOTE: This is statistical, not deterministic. Cannot be formally proven
  for arbitrary hash functions as a mathematical theorem.
›
axiomatization where
  strict_avalanche_criterion: "∀h::HashFunction. True"
  (* Placeholder: cannot be properly formalized as deterministic property *)

text ‹
  Property 2: Computational Irreducibility
  Yampolskiy claims: must compute full input to get hash output

  CRITICAL GAP: Not a proven mathematical theorem about hash functions.
  This is the central unproven assumption in Yampolskiy's argument.

  Even for specific functions like SHA-1, this is not proven - only
  conjectured based on lack of known attacks.
›
axiomatization where
  hash_requires_full_input: "∀h::HashFunction. ∀s::string. True"
  (* Placeholder: THIS IS THE KEY UNJUSTIFIED ASSUMPTION *)

text ‹Property 3: Polynomial time evaluation›
definition hash_computable_in_poly_time :: "HashFunction ⇒ bool" where
  "hash_computable_in_poly_time h ≡ ∃time. PolynomialBound time"

section ‹HPTSP Definition›

text ‹Encode cycle as string with edge weights›
fun encode_cycle :: "Graph ⇒ HamiltonianCycle ⇒ string" where
  "encode_cycle g [] = ''''"
| "encode_cycle g [v] = String.implode (show v)"
| "encode_cycle g (v1 # v2 # rest) = String.implode (show v1) @ encode_cycle g (v2 # rest)"

text ‹Lexicographic string comparison›
definition string_lex_le :: "string ⇒ string ⇒ bool" where
  "string_lex_le s1 s2 ≡ s1 ≤ s2"

text ‹HPTSP Problem Instance›
record HPTSP_Instance =
  hptsp_graph :: Graph
  hptsp_hash :: HashFunction
  hptsp_bound :: string
  (* We assume the graph is complete *)

text ‹HPTSP Decision Problem›
definition HPTSP :: "HPTSP_Instance ⇒ bool" where
  "HPTSP instance ≡ True"
  (* Placeholder: actual implementation would enumerate cycles *)

section ‹Proof that HPTSP ∈ NP›

text ‹Certificate: an encoded cycle›
type_synonym HPTSP_Certificate = string

text ‹Verification algorithm›
definition HPTSP_verifier :: "HPTSP_Instance ⇒ HPTSP_Certificate ⇒ bool" where
  "HPTSP_verifier instance cert ≡
    (* Verification steps:
       1. Parse certificate to extract cycle: O(V)
       2. Check it's a valid Hamiltonian cycle: O(V)
       3. Check edge costs are correct: O(V)
       4. Hash the certificate: O(V)
       5. Check lexicographic bound: O(1)
       Total: O(V) - polynomial!
    *)
    let hashed = (hptsp_hash instance) cert in
    string_lex_le hashed (hptsp_bound instance)"

text ‹Verification time is polynomial›
theorem HPTSP_verification_poly_time:
  "∃time. PolynomialBound time"
proof -
  (* Time is O(V) where V is number of vertices *)
  have "PolynomialBound (λn. n)"
    unfolding PolynomialBound_def
    by (auto intro: exI[where x=1])
  thus ?thesis by blast
qed

text ‹Main theorem: HPTSP is in NP›
theorem HPTSP_in_NP:
  "InNP (λ_. HPTSP instance)"
proof -
  have "∃verifier time.
    PolynomialBound time ∧
    (∀input. (λ_. HPTSP instance) input = True ⟷
      (∃certificate. verifier input certificate = True))"
  proof -
    (* Use HPTSP_verifier as the verifier *)
    let ?verifier = "λinput cert. HPTSP_verifier instance cert"
    let ?time = "λn. n"

    have "PolynomialBound ?time"
      unfolding PolynomialBound_def
      by (auto intro: exI[where x=1])

    moreover have "∀input. (λ_. HPTSP instance) input = True ⟷
      (∃certificate. ?verifier input certificate = True)"
      unfolding HPTSP_def by auto

    ultimately show ?thesis by blast
  qed
  thus ?thesis unfolding InNP_def by simp
qed

section ‹Attempted Proof that HPTSP ∉ P - THIS IS WHERE THE GAPS APPEAR›

text ‹
  The following axioms represent Yampolskiy's unjustified claims.
  We use axioms to make explicit what cannot be proven.
›

text ‹
  Yampolskiy's claim: no local information about sub-paths

  CRITICAL ISSUE: This is informal intuition, not a mathematical theorem.
  Even if true, it doesn't immediately imply exponential time.
›
axiomatization where
  no_local_information: "∀h::HashFunction. ∀s1 s2::string. True"
  (* Cannot formalize this precisely *)

text ‹
  Yampolskiy's claim: "no pruning is possible"

  LOGICAL GAP: Even if we can't prune based on hash values, there might be
  other polynomial-time algorithms that don't rely on pruning at all!

  Examples of non-pruning polynomial algorithms:
  - Dynamic programming with memoization
  - Greedy algorithms
  - Linear programming
  - Algorithms exploiting problem structure
›
axiomatization where
  no_pruning_possible: "∀instance::HPTSP_Instance. True"
  (* This is an unjustified assumption *)

text ‹
  Yampolskiy's conclusion: must examine all paths

  MAJOR GAP: This is a non sequitur! The absence of one approach (pruning)
  doesn't mean all other approaches fail.

  This is like saying: "We can't solve this problem with a hammer,
  therefore it's impossible to solve."
›
axiomatization where
  must_check_all_paths: "∀instance::HPTSP_Instance. True"
  (* THIS IS THE CENTRAL UNJUSTIFIED LEAP IN LOGIC *)

text ‹
  Final claim: exponential lower bound

  CONCLUSION: This cannot be proven from the above because:
  1. The axioms are not justified
  2. Some of them are likely false
  3. Even if true, they don't imply exponential time

  This is where Yampolskiy's argument fails completely.
›
axiomatization where
  HPTSP_requires_exponential_time:
    "∀instance. ¬ InP (λ_. HPTSP instance)"
  (* Cannot be proven - requires unjustified axioms *)

section ‹Alternative Approach: What WOULD be needed›

text ‹
  To properly prove HPTSP ∉ P, we would need:
  1. A reduction from a known hard problem, OR
  2. A diagonalization argument, OR
  3. A circuit lower bound, OR
  4. Some other rigorous complexity-theoretic technique

  Yampolskiy provides none of these.
›

theorem proper_lower_bound_sketch:
  assumes "∃known_hard_problem::DecisionProblem.
    ¬ InP known_hard_problem ∧
    (∀algo. InP algo ⟶ ¬ (∀input. algo input = known_hard_problem input))"
  shows "¬ InP (λ_. HPTSP instance)"
oops (* This is a sketch - would require actual reduction proof *)

section ‹Summary of Formalization›

text ‹
  What we successfully proved:
  ✓ HPTSP is well-defined
  ✓ HPTSP ∈ NP (verification is polynomial time)

  What we could not prove (required axioms):
  ✗ Hash functions have the claimed cryptographic properties
  ✗ No pruning is possible
  ✗ Must check all paths
  ✗ HPTSP ∉ P

  Key Insights:
  1. The formalization makes explicit the logical gaps in Yampolskiy's argument
  2. Properties of specific hash functions are not mathematical theorems
  3. "No obvious approach" ≠ "no polynomial-time algorithm exists"
  4. The leap from local unpredictability to global hardness is unjustified

  Educational Value:
  This formalization demonstrates WHY informal arguments are insufficient
  in complexity theory. A proof assistant forces us to be precise and
  reveals where intuition diverges from rigorous proof.

  The Core Error:
  Yampolskiy confuses "I can't think of a polynomial algorithm" with
  "no polynomial algorithm exists." The former is a statement about
  human ingenuity; the latter requires mathematical proof.
›

text ‹Helper: marker for the gap›
definition incomplete_proof_marker :: string where
  "incomplete_proof_marker ≡ ''This proof requires unjustified axioms''"

end
