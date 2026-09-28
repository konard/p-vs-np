# Changlin Wan (2010) - Refutation

## Why the Proof Fails

Wan's 2010 P=NP attempt contains a fundamental error: **"Up" (union of all decidable languages) equals all of ℕ, making it a trivially useless class**.

## The Fatal Discovery: Up = ℕ

### The Key Theorem

For any natural number x:
- The singleton language L_x = {x} is decidable (a simple equality-checking TM decides it)
- Therefore x ∈ Up (since L_x is decidable and x ∈ L_x)
- This holds for ALL natural numbers x

**Conclusion**: Up = ℕ (the set of all natural numbers)

### Why This Destroys the Paper

The paper attempts to prove P = Up = NP. But if Up = ℕ:
- "P = Up" would mean P = ℕ (every language is in P) → IMPOSSIBLE
- "Up = NP" would mean NP = ℕ → IMPOSSIBLE

The paper's construction is **vacuously trivial** - it constructs a "class" that contains everything.

## The Five Critical Errors

### Error 1: Up = ℕ (trivially)

| Aspect | Paper's Claim | Reality |
|--------|---------------|---------|
| **What is Up** | A meaningful complexity class | The set of ALL natural numbers |
| **Does Up ∈ P?** | Yes (claimed) | Yes, trivially (always-accept TM) |
| **Does Up help prove P=NP?** | Yes | No - it's too broad to be meaningful |

### Error 2: Confusion Between Computability and Complexity

- **Decidable**: can be computed (no time bound)
- **P**: can be computed in **polynomial time**
- **NP**: can be verified in polynomial time

The paper defines Up using decidable languages (computability), then claims Up ∈ P (complexity). These are fundamentally different levels of abstraction.

### Error 3: No Concrete Algorithm

A valid P=NP proof must provide:
- An explicit polynomial-time algorithm for an NP-complete problem, OR
- A rigorous proof of equivalence

Wan's paper provides neither. The claim "Up ∈ P" is asserted without any algorithm or complexity analysis.

### Error 4: Circular Reasoning

The paper's proof of Up ⊆ P is circular:
1. The "recursive TM" decides Up in polynomial time (asserted)
2. Therefore Up ∈ P (assumed conclusion)
3. Therefore P = NP

Step 1 is assumed as a fact without proof. The paper assumes the very thing it needs to prove.

### Error 5: Missing Standard Barriers

Any valid P=NP proof must address:
- **Relativization** (Baker-Gill-Solovay, 1975): Proofs must use non-relativizing techniques
- **Natural Proofs** (Razborov-Rudich, 1997): Cannot be based on easily-computable properties
- **Algebrization** (Aaronson-Wigderson, 2008): Must go beyond algebraic techniques

Wan's abstract argument would relativize (works with any oracle), violating the Baker-Gill-Solovay barrier.

## Formal Refutation Results

The formalizations in this directory prove:

1. **`up_equals_all_nats`**: ∀ x : ℕ, Up x (Up contains every natural number)
2. **`up_trivially_in_P`**: ClassP Up (Up is trivially in P as the all-accepting language)
3. **`wan_proof_vacuous`**: The paper's construction is vacuously trivial

## Why the Author Withdrew

The author's comment upon withdrawal: *"sorry for the wild thoughts and immature article writting"*

The fundamental issue is that the "union of all decidable languages" construction is trivially equal to all of ℕ. The paper attempts to treat this trivial object as a meaningful complexity class, leading to a vacuous "proof."

## Key Lessons

1. **Trivial Constructions Don't Prove Non-Trivial Results**: "All decidable languages" = all languages (trivially), so their union is trivially everything

2. **Computability ≠ Complexity**: Decidability tells you IF something can be computed, not HOW EFFICIENTLY

3. **Concrete Algorithms Required**: P vs NP is about concrete computational complexity - abstract existence arguments are insufficient

4. **Meta-level vs Object-level**: "Union of all decidable languages" is a meta-level construction that doesn't correspond to a useful complexity class

## Mathematical Foundation

### Why Up = ℕ is Trivial

For any x ∈ ℕ:
- Define L_x = {x} (singleton set containing only x)
- L_x is decidable: the TM that accepts x and rejects everything else decides L_x
- L_x ⊆ Up by definition (L_x is decidable)
- x ∈ L_x, therefore x ∈ Up

Since this holds for all x, Up = ℕ. ∎

### Why This Doesn't Prove P = NP

The trivially all-accepting TM decides Up = ℕ in O(1) time (just accept). So yes, Up ∈ P. But this means nothing about P = NP because:
- Up = ℕ is not a complexity-theoretic separator between P and NP
- Every SAT instance has Up-membership trivially; this tells us nothing about SAT

## References

- **Wan, C., & Shi, Z.** (2010). "A Proof for P =? NP Problem." arXiv:1005.3010 [cs.CC] **[WITHDRAWN 2020]**
- **Baker, T., Gill, J., & Solovay, R.** (1975). "Relativizations of the P=?NP Question." *SIAM J. Comput.* 4(4), 431-442.
- **Razborov, A. A., & Rudich, S.** (1997). "Natural Proofs." *J. Comput. Syst. Sci.* 55(1), 24-35.
- **Woeginger's List**: Entry #61 - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
