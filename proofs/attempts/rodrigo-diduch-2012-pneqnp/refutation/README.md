# Rodrigo Diduch (2012) - Refutation

## Why the Proof Fails

Diduch's 2012 P≠NP attempt contains a fundamental logical error: **it conflates
not knowing a polynomial algorithm with proving that none can exist**.

## The Fatal Error: Missing Lower Bound

### The Claim

The paper asserts that P ≠ NP because:
- P and NP have different definitions (deciders vs verifiers)
- NP-complete problems like SAT appear hard
- No polynomial algorithm is currently known for SAT

### Why This Is Not a Proof

Proving P ≠ NP requires establishing a **super-polynomial lower bound**:

```
∀ TM, (TM decides SAT) → time(TM) ∉ polynomial
```

This says: *every* Turing machine that correctly decides SAT requires
super-polynomial time. The paper provides no argument for this claim;
it is treated as obvious from the definitions.

## The Logical Error in Detail

### Diduch's Implicit Reasoning

1. "P uses deterministic polynomial algorithms to *solve* problems"
2. "NP uses polynomial algorithms to *verify* solutions"
3. "Solving is harder than verifying"
4. "Therefore P ≠ NP"

### Why Step 3→4 Fails

Step 3 ("solving is harder than verifying") is an **informal intuition**, not a theorem.
Making it formal requires proving that for *every* polynomial-time verifier for SAT,
no polynomial-time solver exists. This is precisely what P ≠ NP means, so the argument
is circular.

### The Key Distinction

| Type of statement | Example | Sufficient for P≠NP? |
|-------------------|---------|----------------------|
| Definitional difference | "P uses TMs, NP uses verifiers" | No |
| Epistemic observation | "No polynomial SAT solver is known" | No |
| Lower bound theorem | "∀ TM deciding SAT: time(TM) ∉ poly" | Yes |

Diduch provides only the first two; the third is missing.

## Counterexample to the Argument Style

To show why definitional differences are insufficient, consider:

- **Class A**: Problems decidable in O(n²) time
- **Class B**: Problems decidable in O(n³) time

These have different definitions, yet A ⊆ B ⊆ P, and many problems lie in both.
A difference in how classes are defined does not entail a difference in which problems
they contain.

Similarly, P and NP could in principle be equal even though P uses deterministic
solvers and NP uses verifiers. This is what the P vs NP question *asks* — and the
answer requires a proof, not an appeal to definitional differences.

## Known Barriers That Block This Approach

### 1. Relativization (Baker-Gill-Solovay, 1975)

Any argument that works by analyzing definitions of TMs or complexity classes
likely *relativizes* — meaning it holds equally in worlds with an oracle where
P^A = NP^A. Since such oracles exist, a relativizing argument cannot prove P ≠ NP.

Diduch's definitional argument is entirely about the structure of the definitions
of P and NP, making it highly unlikely to be non-relativizing.

### 2. Natural Proofs (Razborov-Rudich, 1997)

Standard "natural" circuit lower bound techniques (which are constructive, large,
and useful) are blocked under the assumption that one-way functions exist.
Any valid P ≠ NP proof must use non-naturalizing techniques.

### 3. Algebrization (Aaronson-Wigderson, 2008)

Further restricts proof strategies by ruling out algebraic extensions of
relativization-based arguments.

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`definition_difference_insufficient`**: Different definitions of P and NP do not
   imply the classes are different
2. **`epistemological_gap`**: Not knowing an algorithm ≠ proving none exists
3. **`lower_bound_is_the_whole_problem`**: What a valid proof would need to supply

## Key Lessons

1. **Definition ≠ Extension**: Two differently-worded definitions can describe the same set
2. **Observation ≠ Impossibility**: Current ignorance does not prove mathematical impossibility
3. **Intuition ≠ Proof**: "Solving feels harder than verifying" is not a theorem
4. **Lower Bounds Are Hard**: Proving super-polynomial lower bounds is the entire difficulty
   of P vs NP; it cannot be bypassed by definitional argument

## References

- **Diduch, G. R.** (2012). "P vs NP". IJCSNS, 12(1), 165–167.
- **Baker, T., Gill, J., & Solovay, R.** (1975). Relativizations of the P=?NP Question.
  SIAM Journal on Computing, 4(4), 431–442.
- **Razborov, A. A., & Rudich, S.** (1997). Natural Proofs.
  Journal of Computer Science and System Sciences, 55(1), 24–35.
- **Aaronson, S., & Wigderson, A.** (2008). Algebrization: A New Barrier in Complexity Theory.
  STOC '08.
- **Woeginger's List**: Entry #81 — https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
