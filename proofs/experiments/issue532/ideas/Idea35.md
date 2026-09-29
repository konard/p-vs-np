# Idea 35 — Exact compression of solution sets

**Verdict:** Refuted as a route (general theorem)

The idea is to decide SAT by compressing the whole solution set of a formula
into a short exact representation, then reading the answer off it. The files
prove that every exact (injective) representation of Boolean functions on `n`
variables gives some function a representation of length at least `2^n`. They
also prove that fewer than `2^b` truth tables can have codes shorter than `b`.
Compact representations therefore exist only for special families. Restricted
to CNF-definable functions, the idea is exactly as hard as SAT itself. The Lean
file proves this in the shared machine model. The open obligation `CompiledSAT`
asks for a `Complexity.Machine` that compiles every instance in polynomial time,
and a polynomial-time machine that reads satisfiability off the compiled
representation. `compiles_iff_inP` proves that such a compilation exists for a
language exactly when it is in P, so `CompiledSAT ↔ InP SAT`
(`compiledSAT_iff`). With `SATHard` (not mechanised) the obligation gives
`PEqualsNP` (`pEqualsNP_of_compiledSAT`).

## 1. The idea at full strength

A CNF formula with `n` variables defines its solution set, a Boolean function
`f : {0,1}^n → {0,1}`. The hope is:

1. There is a **lossless** encoding `rep` of solution sets into short strings
   (for example a decision diagram, a d-DNNF circuit, or a clever succinct
   structure).
2. Satisfiability, model counting, or any other query can be read from
   `rep f` in time polynomial in its length.
3. For every formula `φ`, `rep (sol φ)` is polynomial in `|φ|` and can be
   computed in polynomial time.

(1) + (2) + (3) would give SAT in P, and even #SAT in FP, which would put
P^#P inside P.

The idea mentions "compression" and "solution space structure" in the spirit
of issue #532, Part I, item 2, where information and representation are treated
as the key resource.

## 2. Precise mathematical formulation

- `allInputs n`: the explicit, duplicate-free list of the `2^n` bit strings of
  length `n`.
- `inputsBelow m`: the list of all bit strings of length `< m`. It has
  `2^m - 1` elements.
- `truthTable n f := (allInputs n).map f`, a list of length `2^n`.
- `ofTable n t`: the Boolean function whose truth table is `t`. It is defined by
  recursion on `n`, splitting `t` at `2^(n-1)`.
- `ExactOn n rep := ∀ f g, rep f = rep g → ∀ x, |x| = n → f x = g x`. A
  representation is exact on `n` variables if equal codes imply equal
  functions on `{0,1}^n`.
- `CompactTractableCompilationFor size repSize sat q compile query` means
  `repSize (compile φ) ≤ q (size φ)` for all `φ`, and
  `query (compile φ) = sat φ` for all `φ`. This is a schema: the costs of
  `compile` and `query` are free, so it says nothing about running time.
- Machine model (Lean, shared `Machines` layer; time is the `Run` step count
  of a `Complexity.Machine`):

  ```lean
  def Compiles (L : Language) : Prop :=
    ∃ (m : Machine) (compile : Word → Word) (p : Polynomial) (d : Machine) (q : Polynomial)
      (Query : Language), Machines.Computes m compile p ∧ (∀ x, L x = Query (compile x)) ∧
      Machines.DecidesOn d q (fun w => ∃ x, compile x = w) Query

  /-- Open obligation. -/
  def CompiledSAT : Prop := Compiles Machines.SAT
  ```

  The compiler is a machine running in polynomial time, so the representation
  has polynomial length (`compiles_compact`, from
  `Machines.computes_output_poly`). The query machine is required to be
  correct and polynomial (in the representation length) only on compiled
  representations. This is a promise problem, as in knowledge compilation.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `lossless_injective` | `decode ∘ encode = id` implies `encode` is injective | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `nodup_map_of_inj` | a map that is injective on a duplicate-free list gives a duplicate-free list | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `inj_length_le` | list pigeonhole: an injective map from duplicate-free `l` into `l'` gives `|l| ≤ |l'|` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `allInputs_length` | `|allInputs n| = 2^n` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `allInputs_nodup` | `allInputs n` has no duplicates | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `mem_allInputs` | every `x` lies in `allInputs |x|` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `inputsBelow_length` | exactly `2^m - 1` strings are shorter than `m` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `mem_inputsBelow` | every `x` with `|x| < m` lies in `inputsBelow m` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `no_injective_into_shorter` | an injective code on all `M`-bit strings has a codeword of length `≥ M` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `few_compressible` | for an injective code, at most `2^b - 1` of the `M`-bit strings get codes shorter than `b` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `truthTable_length` | a truth table on `n` variables has length `2^n` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `truthTable_eq_iff` | equal truth tables iff equal functions on `{0,1}^n` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `truthTable_ofTable` | every list of length `2^n` is the truth table of `ofTable n t` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `exact_representation_needs_long_codes` | every exact representation on `n` variables has some `f` with `|rep f| ≥ 2^n` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `compactness_alone_trivial` | compactness without a query cost bound is trivial (identity compilation) | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `decider_gives_compilation` | a SAT decider is a 1-bit compact compilation | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `compilation_decides` | a compact tractable compilation computes `sat` as `query ∘ compile` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `CompactTractableCompilationFor` (def) | the compilation schema with free costs | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `Compiles` (def) | polynomial-time machine compilation plus polynomial-time machine query on compiled representations | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `CompiledSAT` (def) | open obligation: `Compiles Machines.SAT` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `compiles_compact` | a machine compilation has polynomially bounded representations | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `inP_of_compiles` | `Compiles L → InP L` (via `Machines.inP_of_promise_reduction`) | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `inP_sat_of_compiledSAT` | `CompiledSAT → InP Machines.SAT` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `pEqualsNP_of_compiledSAT` | `SATHard → CompiledSAT → PEqualsNP` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `computes_id` | the empty machine computes the identity in zero steps | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `compiles_iff_inP` | `Compiles L ↔ InP L` for every language | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `compiledSAT_iff` | `CompiledSAT ↔ InP Machines.SAT` | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `not_forall_compiles` | non-vacuity: some language has no compact tractable compilation | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |
| `compactTractableCompilationFor_of_compiles` | a machine compilation instantiates the schema (sizes are word lengths, polynomial bound) | [Lean](../lean/Idea35.lean) | [Rocq](../rocq/Idea35.v) |

The rows from `CompactTractableCompilationFor` on have the same names in Rocq.
Implicit Lean arguments are explicit `forall`s in Rocq, and
`compactTractableCompilationFor_of_compiles` uses `@length bool` for the size
functions and `evalPoly r` for the bound.

The Rocq file is constructive, with no classical axioms. The Lean proof of
`no_injective_into_shorter` (and hence of
`exact_representation_needs_long_codes`) uses `Classical.byContradiction`;
the other Lean theorems do not. In Rocq the pigeonhole
step uses the standard library lemma `NoDup_incl_length`. In Lean it is proved
from scratch by erasing elements.

## 4. Complete argument

**Pigeonhole.** Let `l` be duplicate-free and `f` injective on `l`, with every
`f x` in `l'`. Then `map f l` is duplicate-free (`nodup_map_of_inj`) and
included in `l'`. A duplicate-free list included in another list is no longer
than it, so `|l| ≤ |l'|` (`inj_length_le`).

**Counting codes.** There are `2^M` strings of length `M` (`allInputs_length`)
and `2^0 + ... + 2^(M-1) = 2^M - 1` strings of length `< M`
(`inputsBelow_length`). If an injective code sent every `M`-bit string to a
shorter string, pigeonhole would give `2^M ≤ 2^M - 1`, which is false. This is
`no_injective_into_shorter`. In the same way, the strings whose codes have
length `< b` inject into `inputsBelow b`, so there are at most `2^b - 1` of
them (`few_compressible`). For example, with `M = 2^n` and `b = 2^n - 10`,
fewer than one in `2^10` of all truth tables compresses by ten bits.

**From tables to functions.** `truthTable n` and `ofTable n` are mutually
inverse between functions on `{0,1}^n` (up to agreement on length-`n` inputs)
and lists of length `2^n` (`truthTable_eq_iff`, `truthTable_ofTable`). Given an
exact `rep`, the map `t ↦ rep (ofTable n t)` is injective on `allInputs (2^n)`.
If two tables have equal codes, the exactness of `rep` makes the functions equal
on `{0,1}^n`, so their truth tables are equal, and these are the original
tables. Applying `no_injective_into_shorter` with `M = 2^n` gives a function
whose code has length at least `2^n`. This is
`exact_representation_needs_long_codes`.

**Why this does not settle SAT.** The counting argument is about **all**
`2^(2^n)` functions. Solution sets of CNFs of size `s` number at most `2^O(s log s)`,
so a code of length about `|φ|` for them trivially exists: the formula itself
(`compactness_alone_trivial`). The obligation is therefore not size but
**query cost**. A representation that is compact on CNF solution sets and
answers satisfiability in polynomial time is a polynomial-time SAT algorithm.
In the trivial direction, a decider already is a one-bit compilation
(`decider_gives_compilation`). In the other direction, any such compilation
decides SAT (`compilation_decides`). The machine model makes this exact:
`compiles_iff_inP` proves `Compiles L ↔ InP L` for every language. One
direction composes the compiler with the query machine
(`Machines.inP_of_promise_reduction`). For the other, the empty machine
computes the identity in zero steps (`computes_id`), and the decider serves as
the query. So the route "compress the solution space
and then query it" is refuted as a route to P = NP. Either the compression
covers all functions, and then it is impossible, or it covers CNF-definable
functions, and then it is a restatement of the goal.

## 5. Known results and literature

- C. E. Shannon, "The synthesis of two-terminal switching circuits", *Bell
  System Technical Journal* 28, 1949. The counting argument shows that most
  Boolean functions need circuits of size about `2^n / n`. It is the same
  pigeonhole principle as here, applied to circuits instead of strings.
  Formalized here only in the string form.
- R. E. Bryant, "Graph-based algorithms for Boolean function manipulation",
  *IEEE Transactions on Computers* C-35(8), 1986. This paper introduces
  ordered binary decision diagrams (OBDDs), a canonical exact representation
  on which satisfiability and model counting are polynomial in the size of the
  diagram.
- R. E. Bryant, "On the complexity of VLSI implementations and graph
  representations of Boolean functions with application to integer
  multiplication", *IEEE Transactions on Computers* 40(2), 1991. It shows that
  every OBDD for the middle bit of integer multiplication has exponential size,
  whatever the variable order. Not formalized.
- A. Darwiche and P. Marquis, "A knowledge compilation map", *Journal of
  Artificial Intelligence Research* 17, 2002. This paper surveys compilation
  languages (OBDD, d-DNNF, and others) and their succinctness and query
  trade-offs. Not formalized.
- L. G. Valiant, "The complexity of computing the permanent", *Theoretical
  Computer Science* 8, 1979. It defines #P. S. Toda, "PP is as hard as the
  polynomial-time hierarchy", *SIAM J. Computing* 20, 1991, shows that PH is
  contained in P^#P. A compilation supporting polynomial model counting for all
  CNFs would therefore collapse PH to P. Neither is formalized.

## 6. How far the idea can be pushed toward P vs NP

**At full potential**, the idea says: find representations and maps
`compile`, `query` satisfying the schema
`CompactTractableCompilationFor size repSize sat q compile query`, with
`compile` and `query` both running in polynomial time. In the machine model
that is the open obligation `CompiledSAT := Compiles Machines.SAT`. The proved
route is

```lean
theorem pEqualsNP_of_compiledSAT (hard : Machines.SATHard) (h : CompiledSAT) : PEqualsNP
```

Its only hypothesis besides the obligation is `SATHard`, the hardness half of
Cook–Levin (shared layer, not mechanised). `compiledSAT_iff` proves
`CompiledSAT ↔ InP Machines.SAT`, so nothing is gained over the original
problem. `not_forall_compiles` confirms that `Compiles` is not satisfied by
every language, and `compactTractableCompilationFor_of_compiles` shows that the
machine notion is an instance of the schema.

**What the counting shows.** No exact scheme compresses everything
(`exact_representation_needs_long_codes`). Any compression must exploit the
structure of CNF-definable functions. Known compilation languages lose at some
explicit functions. For OBDDs this is Bryant's multiplication bound, and
exponential separations between compilation languages are catalogued by
Darwiche and Marquis.

**Barriers.** Lower bounds for specific compilation languages (OBDDs, d-DNNF)
are known. Proving that *no* polynomial-time compilation with polynomial-time
queries exists means proving SAT ∉ P, i.e. P ≠ NP, so it faces all the
barriers of that problem, including relativization and, for circuit-based
approaches, natural proofs (see Ideas 38 and 39).

**Honest conclusion.** The route is refuted in its general form. In the
restricted form it is equivalent to the open problem. No proof of P = NP or
P != NP follows.

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 7 (counting, compression, or enumeration mistakes):** claims that
  "the solution space can always be stored in polynomial space" contradict
  `exact_representation_needs_long_codes` unless the claim is restricted, and
  then the restriction must be justified.
- **Family 2 (hiding exponential work):** building an OBDD or d-DNNF can take
  exponential time and space. A polynomial query on an exponential object is
  not a polynomial algorithm.
- **Family 5 (solving an easier problem):** compiling a special family (for
  example bounded treewidth CNFs) does not cover all CNFs.
- **Family 12 (smuggling the conclusion):** assuming that a compact tractable
  compilation exists is assuming SAT ∈ P (`compilation_decides`,
  `compiledSAT_iff`).

Audit rule: for any claimed compression, ask (i) is it exact, (ii) what is the
length bound for **every** input formula, and (iii) what is the time to build
it. If (ii) and (iii) are both polynomial, the claim is P = NP, and it needs a
proof, not an example.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea35.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea35.v
rm -f proofs/experiments/issue532/rocq/Idea35.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea35.aux
```

Both commands print nothing on success.
