# Refutation of Du's 2010 P=NP Attempt

## Why the Proof Fails

Du's 2010 P=NP attempt contains a critical flaw in **Algorithm 1, Step 3**:
the intersection operation on useful units is **unsound** — it eliminates valid
satisfying assignments, causing the algorithm to produce false negatives
(reporting UNSAT for satisfiable formulas).

## The Fatal Error: Incorrect Intersection in Step 3

### What Step 3 Does

For all pairs of literals (x, y) in distinct 3-unit layers that are NOT contradiction pairs:

```
U(x) ← U(x) ∩ U(y)
U(y) ← U(x) ∩ U(y)
```

### Why This Is Wrong

**Du's assumption:** Any valid satisfying assignment must be compatible with both
U(x) and U(y), so the intersection captures exactly the valid assignments.

**The reality:** A satisfying assignment may make x true (using only U(x)) OR make y
true (using only U(y)) — it does NOT need to be in both. The formula allows
independent solution branches.

**The consequence:** Step 3 prematurely eliminates valid solution branches whenever
U(x) ∩ U(y) = ∅, even if the formula is satisfiable via a branch using only U(x)
or only U(y).

## The Counter-Example (He et al., 2024)

### Construction

He, Y. et al. (arXiv:2404.04395) construct the following family of satisfiable
3-CNF formulas that Algorithm 1 incorrectly reports as UNSAT:

```
φₙ = (s ∨ t ∨ ¬c) ∧ (¬s ∨ ¬t ∨ r) ∧ C₁ ∧ ... ∧ Cₙ ∧ (a ∨ b ∨ c)
```

where:
- Variables: s, t, c, r, a, b, α (and variables in C₁, ..., Cₙ)
- C₁, ..., Cₙ can be any clauses satisfying Algorithm 1's preconditions

### Why φₙ Is Satisfiable

The assignment:
- s = true, t = false
- c = true, r = false
- a = true (satisfies the last clause via a)

satisfies:
- (s ∨ t ∨ ¬c): s = true ✓
- (¬s ∨ ¬t ∨ r): ¬t = true ✓
- (a ∨ b ∨ c): a = true ✓
- All C₁, ..., Cₙ: can be satisfied by appropriate assignment

Therefore φₙ is satisfiable.

### What Algorithm 1 Does

1. **Build checking tree:** Algorithm 1 builds the checking tree T for φₙ.
2. **Compute useful units:** For literal α (variable alpha), Algorithm 1 computes
   U(α) = {s, t} (s and t are forced by unit propagation from α's assumption).
3. **Test contradiction pair:** Algorithm 1 checks if (c, α) is a contradiction pair.
   To do this, it removes ¬c and ¬α from T and applies Step 3.
4. **Step 3 eliminates s and t:** After removing ¬c and ¬α, the intersection
   in Step 3 forces U(α) ← U(α) ∩ U(β) = {s, t} ∩ ∅ = ∅ for some literal β.
5. **False UNSAT:** Since U(α) = ∅, Algorithm 1 returns UNSAT.

### Why This Creates an Infinite Family

The clauses C₁, ..., Cₙ can be any clauses satisfying Algorithm 1's structural
assumptions. This means there are infinitely many choices of C₁, ..., Cₙ, giving
an infinite family of satisfiable formulas that Algorithm 1 incorrectly rejects.

## Formal Refutation

### Main Theorem

```
Du's Algorithm 1 is NOT a correct decider for 3SAT.
Formally:
  ¬ (∀ f : CNFFormula, is3CNF(f) → (duAlgorithm1(f) = SAT ↔ isSatisfiable(f)))
```

**Proof:** By the He et al. counter-example:
- φ₁ is a 3-CNF formula (all clauses have ≤ 3 literals)
- φ₁ is satisfiable (explicit assignment given above)
- duAlgorithm1(φ₁) = false (UNSAT) by the incorrect Step 3 intersection
- This contradicts correctness: duAlgorithm1(φ₁) = true ↔ isSatisfiable(φ₁)

### The Step 3 Intersection Is Unsound

```
∃ u₁ u₂ : UsefulUnits,
  u₁ ≠ u₂  ∧
  ¬isContradictionPair(u₁.literal, u₂.literal)  ∧
  (duIntersect(u₁, u₂)).units = []  ∧
  ∃ assignment, it_satisfies_the_formula
```

**Proof:** Take:
- u₁ = UsefulUnits(α, [s, t])  (useful units of α contain s and t)
- u₂ = UsefulUnits(β, [])      (useful units of β are empty after removing ¬c, ¬α)
- duIntersect(u₁, u₂).units = [s, t] ∩ [] = []
- But φ₁ is still satisfiable!

## Limitations of the Formal Proofs

The Lean and Rocq formalizations in this directory use:
- **`sorry` / `Admitted`** for the counter-example construction, because formalizing
  Du's checking tree construction in full detail would require a substantial
  implementation. The key axioms `heCounterExample_is_satisfiable` and
  `duAlgorithm_fails_on_counterexample` capture the He et al. result.
- **Axioms** for the checking tree internals, since the error is in Step 3, not the
  tree construction.

Despite these limitations, the formalizations correctly capture:
1. The structure of Algorithm 1 (including the flawed Step 3)
2. Why the intersection is unsound (as a proven theorem about the duIntersect function)
3. The logical connection between Step 3's unsoundness and Algorithm 1's incorrectness

## Key Lessons

1. **Pruning Must Be Sound**: In combinatorial search algorithms, any operation that
   eliminates candidate solutions must be proven to never eliminate valid solutions.
   Du's Step 3 fails this criterion.

2. **Independent Solution Branches**: When a formula has multiple independent ways
   to be satisfied, an algorithm must not assume they are mutually constrained.
   The intersection operation incorrectly assumes mutual constraint.

3. **2SAT vs 3SAT Gap**: The complexity gap between 2SAT (polynomial) and 3SAT
   (NP-complete) is fundamental. No polynomial-time algorithm can bridge this gap
   unless P = NP, which is widely believed to be false.

4. **Counter-Examples Are Decisive**: A single counter-example (or infinite family)
   is sufficient to refute an algorithmic claim. He et al.'s construction is clean
   and definitive.

5. **Revision Does Not Fix Fundamental Errors**: The paper's 95 revisions have not
   fixed the fundamental issue with Step 3. Fundamental logical errors cannot be
   patched away without changing the core algorithm.

## References

- **He, Y. et al.** (2024). "A Critique of Du's 'A Polynomial-Time Algorithm for 3-SAT'".
  arXiv:2404.04395. https://arxiv.org/abs/2404.04395

- **Du, L.** (2010). "A Polynomial time Algorithm for 3SAT". arXiv:1004.3702.
  https://arxiv.org/abs/1004.3702 (v95, December 2025)

- **Woeginger's List**, Entry #60.
  https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
