# Refutation: Plotnikov 2011 P≠NP

## Why the Proof Fails

Plotnikov's 2011 P≠NP attempt contains multiple fundamental errors that invalidate the proof.

## Fatal Error 1: Circular Diagonal Construction

### The Claimed Construction

Plotnikov constructs a "diagonal graph" H_i for each polynomial-time algorithm A_i such that:

> H_i is 3-colorable **if and only if** A_i rejects H_i

### Why This Is Circular

To **build** H_i, you need to know whether H_i is 3-colorable.
But H_i's colorability is **defined** by what A_i outputs on H_i.
And A_i's output on H_i requires H_i to **already exist** as input.

This creates a circular dependency:
```
H_i is defined → requires knowing is3Colorable(H_i)
                → requires A_i(H_i)
                → requires H_i to already be defined
```

There is no well-defined starting point. H_i does not exist as a concrete graph.

### Why This Differs From Valid Diagonalization

Turing's halting problem diagonalization:
```
D(i) = run M_i on input i; if M_i halts → loop; if M_i loops → halt
```
- Input `i` is a **natural number** (an index)
- `i` is defined **independently** of D's construction
- No circularity: D exists before we ask "what does D do on input D's own index?"

Plotnikov's construction:
```
H_i = a graph that is 3-colorable iff A_i(H_i) = false
```
- H_i must be a **concrete graph** (the input to A_i)
- H_i's definition depends on **A_i's output on H_i**
- H_i cannot be defined before A_i runs on it

The critical difference: Turing's diagonalization asks about a **function's behavior on its own index** (a number), not about **a graph's intrinsic combinatorial property** (colorability) defined by the function's output.

## Fatal Error 2: Relativization Barrier

The **Baker-Gill-Solovay theorem** (1975) establishes that:

> There exist oracles A and B such that P^A = NP^A and P^B ≠ NP^B.

**Consequence**: Any proof technique that **relativizes** (works in the presence of any oracle) cannot separate P from NP.

**Diagonalization relativizes**: Plotnikov's diagonal construction would work equally well relative to any oracle, since diagonalization arguments are oracle-independent. Therefore, even if the construction were well-defined, the approach cannot prove P ≠ NP by the Baker-Gill-Solovay theorem.

This is a **structural barrier** — not just a gap in the proof, but a theorem showing that the entire proof strategy is insufficient.

## Fatal Error 3: Incorrect Fixed-Point Argument

### What Would Be Needed

A valid diagonal construction for P vs NP would need to find a graph G* such that:
- G* is 3-colorable ↔ some condition involving a polynomial-time algorithm's behavior on G*

By the **Recursion Theorem** (Kleene), such fixed-points exist for computable functions — but:
1. Even if G* is well-defined computably, it may not be well-defined as a concrete small graph
2. 3-colorability is a **combinatorial property**, not a computational one; the graph G* would need to encode the algorithm's computation as graph structure, which requires exponential blowup
3. The resulting G* might not be constructable in polynomial time

### The Recursion Theorem Cannot Help Here

The Recursion Theorem provides: for any computable f, there exists e such that M_e ≡ M_{f(e)}.

This applies to **Turing machines** (algorithms), not to **graphs** (combinatorial objects). The theorem cannot directly give a graph whose 3-colorability mirrors an algorithm's output.

## Fatal Error 4: Confusion About What Needs to Be Proved

### What P ≠ NP Requires

To prove P ≠ NP, one must show:
> For ALL polynomial-time algorithms A, A does not correctly decide 3-COL on ALL inputs.

### What Plotnikov's Argument (If Valid) Would Show

Even granting the circular diagonal construction, the argument shows only:
> A specific algorithm (the one in the enumeration at the diagonal index) fails on a specific input (the diagonal graph).

But a correct proof of P ≠ NP must:
- Work for **all** polynomial-time algorithms simultaneously
- Show that each such algorithm fails on **some** input (not necessarily the same one)
- Handle algorithms with arbitrary internal structure, including ones not anticipated by the proof

A diagonalization that constructs one problematic input for each algorithm is the right **style** of argument, but requires the construction to be **well-defined** for each algorithm.

## The Comparison Table

| Property | Turing's Halting Diagonalization | Plotnikov's Diagonal |
|----------|----------------------------------|----------------------|
| **Object being diagonalized** | Natural numbers (machine indices) | Graphs (combinatorial objects) |
| **Self-referential input** | Integer i (index of D itself) | Graph H_i (the actual input) |
| **Circularity** | None — i is defined before D | Circular — H_i needs its own colorability |
| **Well-defined?** | Yes | No |
| **Relativizes?** | Yes | Yes |
| **Can separate P from NP?** | No (by Baker-Gill-Solovay) | No |

## Historical Context

This attempt is one of many failed P≠NP proofs that use diagonalization. The Baker-Gill-Solovay theorem (1975) established that diagonalization-based arguments cannot resolve P vs NP, which is why:

- Despite decades of work, no valid diagonalization-based P≠NP proof exists
- The theoretical CS community now focuses on **non-relativizing** proof techniques
- Current barriers (Natural Proofs, Algebrization) show even stronger limitations on possible proof approaches

Plotnikov himself had previously claimed P=NP (entries #2 and #39), making the reversal to P≠NP particularly notable — neither direction has a correct proof from these arguments.

## Formal Refutations

- `lean/PlotnikovRefutation.lean` - Lean 4 formalization of why the proof fails
- `rocq/PlotnikovRefutation.v` - Rocq formalization of why the proof fails
