# Idea 07 — Lossless compression (pigeonhole and incompressibility)

**Verdict:** Refuted as a route (general theorem)

This route hopes to shrink instances, witnesses, or search spaces by lossless
compression until brute force becomes cheap. Counting rules it out. There are
`2^n` strings of length `n` but only `2^n − 1` shorter strings, so every encoder
that is injective on `n`-bit strings leaves some string unshortened
(`no_universal_compression`). For every decoder, some `n`-bit string has no
description shorter than `n` bits (`incompressible_exists`), and at most
`2^m − 1` strings have descriptions shorter than `m` (`count_describable_le`).
Compression only works on structured families, such as runs of one repeated
bit (`runCode_injective_on_runs`), and finding that structure is the hard
part.

## 1. The idea at full strength

Ambitious version (direction P = NP): compress every SAT instance, or the
space of its candidate witnesses, into a representation with polynomially
many possibilities, and then search the compressed space. A weaker form claims
that "generalization is compression" gives a universal shortcut: a short
program explains every dataset better than a lookup table.

Source in issue #532: Part I item 4 ("Lookup tables are not shortest in
general. Generalization is compression. Compression is hypothesis search.
Hypothesis search is NP-hard" and "Compression ↔ complexity bridge"), Part I
item 3 ("Finding the shortest program is undecidable"; "When restricted to
finite observed data … decidable but NP-hard (via generalization/compression)"),
and Part II Phase 4 ("counting arguments … compression-only arguments …
Attempt formal proofs → record exact failure points"). The failure point
recorded here is the counting theorem `no_universal_compression`.

## 2. Precise mathematical formulation

* **Strings.** `Str = List Bool`. `allStrings n` enumerates the strings of
  length `n`. `shorter n` enumerates the strings of length `< n`.
* **Lossless on a slice.** `InjectiveOnLength enc n :⇔ ∀ x y, |x| = n → |y| = n → enc x = enc y → x = y`.
  Nothing is assumed about computability or running time of `enc`.
* **Descriptions.** For a decoder `dec : Str → Str` (any description method,
  e.g. "run program `p`"), `Describable dec m x :⇔ ∃ p, |p| < m ∧ dec p = x`.
  Kolmogorov complexity relative to `dec` is the least `m` with
  `Describable dec (m+1) x`.
* **Runs.** `run b n = b^n` (the bit `b` repeated `n` times). `runCode x = [head x]`.
* **The claim the route needs.** An encoder that is injective on all instances
  of length `n` and maps each of them to length `< n` (or to length `≤ p(n)`
  for a set of size `2^n`, where `p(n) < n`).

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `length_allStrings` | `|allStrings n| = 2^n`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `mem_allStrings_iff` | `v ∈ allStrings n ↔ |v| = n`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `nodup_allStrings` | `allStrings n` has no repetitions. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `length_shorter` | `|shorter n| = 2^n − 1`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `mem_shorter_iff` | `v ∈ shorter n ↔ |v| < n`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `pigeonhole` | If `L` has no duplicates and every element of `L` is in `M`, then `|L| ≤ |M|`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `nodup_map_of_injOn` | A map injective on a duplicate-free list `L` gives a duplicate-free `L.map f`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `no_universal_compression` | `InjectiveOnLength enc n → ∃ x, |x| = n ∧ n ≤ |enc x|`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `shortening_forces_collision` | If `|enc x| < n` for every `x` with `|x| = n`, then `∃ x y, |x| = n ∧ |y| = n ∧ x ≠ y ∧ enc x = enc y`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `describable_iff` | `Describable dec m x ↔ x ∈ (shorter m).map dec`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `count_describable_le` | For every `dec, n, m`: the number of strings in `allStrings n` that lie in `(shorter m).map dec` is `≤ 2^m − 1`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `incompressible_exists` | For every `dec` and `n`: `∃ x, |x| = n ∧ ¬ Describable dec n x`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `runCode_injective_on_runs` | For `n ≥ 1`: `runCode (run b n) = runCode (run c n) → run b n = run c n`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |
| `runCode_length` | `|runCode (run b n)| = 1`. | [Idea07.lean](../lean/Idea07.lean) | [Idea07.v](../rocq/Idea07.v) |

Lean's `pigeonhole` is proved directly by induction on `L`, removing the
matched element from `M` with `List.erase`. The Rocq proof uses the Stdlib
lemma `NoDup_incl_length`. In Rocq the existence theorems are proved
constructively by `existsb` search over the finite lists (`collides`, `inb`
are the boolean tests). Not machine-checked: the literature results in Section 5.

## 4. Complete argument

**Counting.** `allStrings (n+1)` is `allStrings n` prefixed with `false`,
followed by `allStrings n` prefixed with `true`. So its length doubles, and it
has no duplicates because the two halves differ in the first bit. `shorter`
concatenates `allStrings 0, …, allStrings (n−1)`, so its length is
`1 + 2 + … + 2^(n−1) = 2^n − 1`.

**Pigeonhole.** If `x :: L` has no duplicates and is contained in `M`, then
`x ∈ M`, and `L` is contained in `M.erase x` (elements of `L` differ from `x`).
The erased list has length `|M| − 1`, so induction gives `|L| ≤ |M| − 1`.

**No universal compression.** Suppose `enc` is injective on length-`n` strings
and shortens all of them. Then `(allStrings n).map enc` has no duplicates and
lies inside `shorter n`. Pigeonhole gives `2^n ≤ 2^n − 1`, a contradiction.
The contrapositive: an encoder that shortens every string collides, so it is lossy.

**Incompressibility.** Every `x` describable in `< m` bits is `dec p` for one
of the `2^m − 1` strings `p ∈ shorter m`. So the describable `n`-bit strings,
as a duplicate-free sublist of `allStrings n`, lie inside a list of length
`2^m − 1`. With `m = n`, some `n`-bit string is not describable. With
`m = n − c`, at most `2^(n−c) − 1 < 2^n / 2^c` of the `2^n` strings compress by
`c` bits. Worked example: `n = 20`, `c = 10`. At most `1023` of the `1 048 576`
strings of length 20 have descriptions of length `≤ 9`, which is under 0.1%.

**Structure.** The runs `0^n` and `1^n` differ in their first bit, so
`runCode` separates them and their description length is 1 instead of `n`.
The code is lossy on general strings. It works only because the family has 2
members. Compression is always relative to a family: a family of size `N`
needs about `log₂ N` bits, and the family of *all* SAT instances or all
assignments has no such shortcut.

**What this rules out and what it does not.** It rules out "compress every
instance or every candidate solution losslessly" as a way to shrink search.
It does *not* say that SAT instances have no exploitable structure. Any
algorithm, including a polynomial-time SAT solver if one exists, can be read as
exploiting structure. The theorem only shows that such structure cannot come
from compression alone.

## 5. Known results and literature

* A. N. Kolmogorov, "Three approaches to the quantitative definition of
  information", *Problems of Information Transmission* 1(1), 1965.
  Defines description complexity. (Not formalized beyond the counting core.)
* M. Li and P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*, Springer (1st ed. 1993; later editions). Covers the
  incompressibility method: at least `2^n − 2^(n−c) + 1` strings of length
  `n` have complexity `≥ n − c`. Also covers the uncomputability of
  Kolmogorov complexity. (Only the counting part is formalized here, as
  `count_describable_le` and `incompressible_exists`. Uncomputability is not.)
* C. E. Shannon, "A mathematical theory of communication", *Bell System
  Technical Journal* 27, 1948. Lossless codes cannot beat entropy on average.
  (Not formalized.)
* V. Kabanets and J.-Y. Cai, "Circuit minimization problem", STOC 2000.
  Studies MCSP (given a truth table and `s`, is there a circuit of size `≤ s`?).
  They show that NP-hardness of MCSP under certain natural reductions would
  imply circuit lower bounds that are currently out of reach. Whether MCSP is
  NP-complete is open. This is the "deciding compressibility" side of
  the idea. (Not formalized.)

## 6. How far the idea can be pushed toward P vs NP

**At full potential.** Compression can shrink a *family* of size `N` to
`⌈log₂ N⌉` bits. So compression can only help when the problem forces the
relevant objects into a small, efficiently describable family. The run family
proved here is the formal example. (Informally, Horn-SAT is decided through
its unique minimal model; this is an illustration, not a theorem of this
file, and polynomial-time classes such as 2-SAT can have exponentially many
solutions, so small solution families are not necessary for tractability.)

**Remaining obligation.** The universal version is refuted outright, so there
is nothing left to prove for it, and no `def` obligation is introduced. The
structured version turns into two separate questions. (a) Identify a family
that contains every relevant instance or witness and is small. For all of SAT,
the witness family is all `2^n` assignments, and counting shows it cannot be
shrunk losslessly. (b) Decide membership and decode efficiently. That is an
algorithmic question of the same kind as Idea 01's `PolySATDecider`. Deciding
how compressible a given string is (MCSP-type problems, or time-bounded
Kolmogorov complexity) is itself a problem whose NP-hardness is open for MCSP
itself (Kabanets–Cai explain why proving it would be difficult).

**Barriers.** Counting is unconditional and cannot be circumvented. Kolmogorov
complexity is uncomputable, so an "optimal compressor" cannot be an algorithm
(this matches issue Part I item 3). Resource-bounded variants are where the
real open questions live.

## 7. Failure modes this idea catches

* **Counting/compression mistakes**
  ([error family 7](../../../attempts/COMMON_ERRORS.md#7-counting-compression-or-enumeration-mistakes)):
  any claim that a scheme shortens *all* inputs, or represents `2^n`
  possibilities in fewer than `n` bits, contradicts `no_universal_compression`.
* **Encoding-size mistakes**
  ([family 17](../../../attempts/COMMON_ERRORS.md#17-encoding-size-bit-complexity-or-parameter-mistakes)):
  a "polynomial-size" compressed form of an exponential object must come with
  a proof that the object belongs to a small family. Otherwise the size bound is
  false for most inputs (`count_describable_le`).
* **Hidden exponential work**
  ([family 2](../../../attempts/COMMON_ERRORS.md#2-hiding-exponential-work-in-a-claimed-polynomial-algorithm)):
  a decoder that is allowed to run for exponential time moves the cost
  somewhere else rather than removing it.
* **Special-case success**
  ([family 5](../../../attempts/COMMON_ERRORS.md#5-solving-an-easier-special-approximate-or-different-problem)):
  compressing a structured family (`runCode_injective_on_runs`) does not
  transfer to all instances.
* **Provability vs computability**
  ([family 10](../../../attempts/COMMON_ERRORS.md#10-confusing-provability-computability-decidability-and-complexity)):
  "the shortest description" exists for each string but is not computable,
  and time-bounded versions have their own complexity questions.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea07.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea07.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea07.{vo,vok,vos,glob}` and
`.Idea07.aux` files.
