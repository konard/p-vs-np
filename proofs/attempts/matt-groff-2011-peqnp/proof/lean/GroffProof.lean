/-
  GroffProof.lean - Forward formalization of Matt Groff's 2011 P=NP attempt

  This file formalizes Groff's CLAIMED proof that P = NP via a polynomial-time
  algorithm for k-SAT using linear algebra on finite fields.

  Reference: arXiv:1106.0683v2 "Towards P = NP via k-SAT: A k-SAT Algorithm
  Using Linear Algebra on Finite Fields" by Matt Groff (2011).

  The algorithm encodes each Boolean clause as a polynomial whose 2^V
  coefficients track which truth assignments satisfy the clause. By manipulating
  these polynomials using multiplication and addition in a finite field GF(p),
  the algorithm attempts to determine the number of satisfying assignments in
  polynomial time.
-/

namespace GroffProofAttempt

-- ============================================================
-- Basic complexity definitions
-- ============================================================

def TimeComplexity := Nat → Nat

def isPolynomial (T : TimeComplexity) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

-- ============================================================
-- k-SAT Problem Definition
-- ============================================================

-- A truth assignment maps each variable index to a Bool value
def TruthAssignment (numVars : Nat) := Fin numVars → Bool

-- A literal: variable index and polarity (positive or negative)
structure Literal where
  varIdx : Nat
  positive : Bool

def Clause := List Literal

-- A k-SAT instance
structure KSATInstance where
  numVars : Nat
  numClauses : Nat
  clauses : List Clause

-- Whether an assignment satisfies a literal
def Literal.satisfiedBy (l : Literal) (numVars : Nat) (assign : TruthAssignment numVars) : Bool :=
  if h : l.varIdx < numVars then
    if l.positive then assign ⟨l.varIdx, h⟩ else !assign ⟨l.varIdx, h⟩
  else false

-- Whether an assignment satisfies a clause
def Clause.satisfiedBy (c : Clause) (numVars : Nat) (assign : TruthAssignment numVars) : Bool :=
  c.any (fun l => l.satisfiedBy numVars assign)

-- Whether an assignment satisfies all clauses
def KSATInstance.satisfiedBy (inst : KSATInstance) (assign : TruthAssignment inst.numVars) : Bool :=
  inst.clauses.all (fun c => c.satisfiedBy inst.numVars assign)

-- k-SAT decision problem: does a satisfying assignment exist?
def kSATDecision (inst : KSATInstance) : Prop :=
  ∃ assign : TruthAssignment inst.numVars, inst.satisfiedBy assign = true

-- ============================================================
-- Clause Polynomials (Section 2 of Groff 2011)
-- ============================================================

-- A clause polynomial has one coefficient per truth assignment.
-- For V variables, there are 2^V truth assignments.
-- The coefficient at index i is 1 if assignment i satisfies the clause, 0 otherwise.
--
-- CRITICAL NOTE: This representation has size 2^numVars (EXPONENTIAL).
-- Groff's paper does not acknowledge this exponential size as a bottleneck.
def ClausePolynomial (numVars : Nat) := Fin (2 ^ numVars) → Nat

-- The "function of ones": all coefficients are 1
def functionOfOnes (numVars : Nat) : ClausePolynomial numVars :=
  fun _ => 1

-- Bit m of natural number i (for building truth assignments from indices)
def getBit (i m : Nat) : Bool := (i / 2 ^ m) % 2 == 1

-- The truth assignment encoded by index i (bit j of i = value of variable j)
def truthAssignmentFromIndex (numVars : Nat) (i : Nat) : TruthAssignment numVars :=
  fun v => getBit i v.val

-- The clause polynomial for variable x_m:
-- coefficient at index i = 1 iff bit m of i is 1 (x_m = true in assignment i)
def singleVarPolynomial (numVars m : Nat) : ClausePolynomial numVars :=
  fun i => if getBit i.val m then 1 else 0

-- The clause polynomial for a clause:
-- coefficient at index i = 1 iff assignment i satisfies the clause
def clausePolynomialFromClause (numVars : Nat) (c : Clause) : ClausePolynomial numVars :=
  fun i =>
    let assign := truthAssignmentFromIndex numVars i.val
    if c.satisfiedBy numVars assign then 1 else 0

-- ============================================================
-- Modified Clause Polynomials (Section 3 of Groff 2011)
-- ============================================================

-- Before multiplication, coefficients are transformed: 0 → 1, 1 → a (for field element a)
-- This is: h(x) = a · f(x) + (f(1) - f(x))
def modifyForMultiplication (numVars p a : Nat) (f : ClausePolynomial numVars)
    : ClausePolynomial numVars :=
  fun i => if f i == 1 then a % p else 1 % p

-- ============================================================
-- Counting Satisfying Assignments
-- ============================================================

-- Count satisfying assignments by iterating over all indices
def countSatisfyingAux (inst : KSATInstance) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let i := 2 ^ inst.numVars - (n + 1)
      let assign := truthAssignmentFromIndex inst.numVars i
      (if inst.satisfiedBy assign = true then 1 else 0)
      + countSatisfyingAux inst n

-- Total count of satisfying truth assignments
def countSatisfying (inst : KSATInstance) : Nat :=
  countSatisfyingAux inst (2 ^ inst.numVars)

-- ============================================================
-- Groff's Claimed Algorithm (Sections 3-8 of Groff 2011)
-- ============================================================

-- GROFF'S CLAIM: The finite field linear system correctly computes countSatisfying mod p.
--
-- The claimed algorithm:
-- 1. Choose prime p > (2n)^2
-- 2. Choose evaluation point x = c (c > 1)
-- 3. Evaluate modified clause polynomials at x = c modulo p
-- 4. Use second-order differences to find matching c₀, c₁ values
-- 5. Solve a 2×2 linear system in GF(p) to get b₂ = count mod p
--
-- This claim CANNOT be formally proved because:
-- (a) Single-point evaluation collapses 2^V coefficients to 1 value, losing information
-- (b) The linear system operates mod p, not over the integers
-- (c) The "count" obtained mod p is not guaranteed to reflect the true count
--
-- This axiom captures Groff's claim that the finite field system is correct.
-- Note: p is assumed to be prime (p > 1 and p has no divisors other than 1 and p).
-- We do not use Nat.Prime here (which requires Mathlib) but instead treat p as a
-- parameter with the implicit assumption that the caller provides a prime.
axiom groff_claim_finite_field_system_correct :
    ∀ (inst : KSATInstance) (p : Nat) (_hp : p > 1) (a₀ a₁ : Nat),
      ∃ (b₂ : Nat),
        b₂ % p = (countSatisfying inst) % p
-- Cannot be proved: single-point evaluation does not faithfully encode
-- the count of satisfying assignments. See refutation/ directory.

-- ============================================================
-- Complexity Claims (Sections 7-8 of Groff 2011)
-- ============================================================

-- Groff claims the algorithm runs in O(P · V(n+V)²) time.
-- This expression IS polynomial in P, V, n — but crucially does NOT account
-- for the exponential size (2^V) of each clause polynomial object.
axiom groff_claim_polynomial_time :
    ∀ (P : Nat),
      isPolynomial (fun n => P * n * (n + n) ^ 2)
-- Cannot be proved correctly: the true complexity includes a factor of 2^V
-- from constructing and operating on the clause polynomials.
-- The actual runtime is O(P · V(n+V)² · 2^V), which is EXPONENTIAL.

-- ============================================================
-- The Main Claim (Theorem 1 of Groff 2011)
-- ============================================================

-- The satisfiability decision based on Groff's count
-- Returns true if the count of satisfying assignments is nonzero
-- (In the actual algorithm, this is approximated via the finite field linear system)
def groffDecides (inst : KSATInstance) : Bool :=
  countSatisfying inst > 0

-- GROFF'S MAIN CLAIM: The algorithm correctly decides k-SAT in polynomial time.
--
-- This claim CANNOT be formally proved because:
-- (a) Single-point evaluation loses information about individual assignments
-- (b) The algorithm is probabilistic, not deterministic (has error probability ε > 0)
-- (c) The clause polynomials have exponential size 2^V
axiom groff_main_claim :
    ∀ (inst : KSATInstance),
      (groffDecides inst = true ↔ kSATDecision inst)
-- A formal proof would require showing the finite field system correctly
-- computes the count, that the algorithm is deterministic, and that runtime
-- is polynomial. All three fail. See refutation/ directory.

-- ============================================================
-- P = NP Claim (Section 9 of Groff 2011)
-- ============================================================

-- Placeholder for k-SAT being in P
def kSATinP : Prop :=
  ∃ (T : TimeComplexity), isPolynomial T ∧
  ∀ (inst : KSATInstance),
    ∃ (decisionBit : Bool),
      decisionBit = true ↔ kSATDecision inst

-- GROFF'S CONCLUSION: k-SAT ∈ P, hence P = NP
-- This follows (conditionally) from groff_main_claim and groff_claim_polynomial_time,
-- but those axioms are not proved — they are admitted claims that fail.
axiom groff_conclusion_kSAT_in_P : kSATinP

end GroffProofAttempt
