/-!
# Issue #532, Idea 16: diagonalization and relativization

Proved for all enumerations, oracles and parameters:

* `diag_ne`, `no_enumeration_of_all`: Cantor/Turing diagonal. For every
  enumeration `e : ℕ → ℕ → Bool`, the language `diag e n = !(e n n)` differs
  from every `e i`.
* `hierarchy_abstract`, `hierarchy_strict`: the abstract time-hierarchy
  argument. If a class `C` is enumerated by `e` and a universal evaluator `u`
  satisfies `u i x = e i x`, the diagonal language is decidable with one query
  to `u` but is not in `C`. So `C` is strictly smaller than the class of
  one-query-to-`u` languages.
* `diag_relativizes`, `hierarchy_relativizes`, `diagTech_relativizing`: both
  arguments go through verbatim for every oracle world `O : ℕ → Bool`, because
  they use only the enumeration/simulation interface. The technique relativizes.
* `no_relativizing_proof`, `relativizing_cannot_prove`,
  `diagonalization_cannot_prove`, `ingredient_necessary`: a statement that
  fails in some oracle world has no relativizing proof. Baker–Gill–Solovay
  (1975, not formalized here) give an oracle `A` with `P^A = NP^A` and an
  oracle `B` with `P^B ≠ NP^B`. So pure diagonalization settles P vs NP in
  neither direction.
* `oracle_adversary`, `testLang_one_certificate`: the query-complexity core of
  the BGS oracle `B`. Any deterministic query algorithm (decision tree) making
  fewer than `2^n` queries is wrong, on some oracle, about the test language
  "some string of length `n` is in `O`". A single certificate query verifies
  membership.

Verdict: pure diagonalization is refuted as a route to P vs NP, in full
strength, by the published BGS theorem. The formal core is the proof that the
diagonal argument relativizes. The open obligation `NonRelativizingIngredient`
is only defined. Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea16

/-! ## Cantor/Turing diagonal -/

/-- The diagonal language of an enumeration. -/
def diag (e : Nat → Nat → Bool) : Nat → Bool := fun n => !(e n n)

/-- The diagonal language differs from every enumerated language (at input `i`). -/
theorem diag_ne (e : Nat → Nat → Bool) (i : Nat) : diag e ≠ e i := by
  intro h
  have h1 : diag e i = e i i := congrFun h i
  unfold diag at h1
  rcases Bool.eq_false_or_eq_true (e i i) with hb | hb <;> simp [hb] at h1

/-- No enumeration `ℕ → (ℕ → Bool)` lists all languages. -/
theorem no_enumeration_of_all (e : Nat → Nat → Bool) : ∃ L : Nat → Bool, ∀ i, e i ≠ L :=
  ⟨diag e, fun i h => diag_ne e i h.symm⟩

/-! ## Abstract hierarchy theorem -/

/-- `e` enumerates exactly the class `C`. -/
def Enumerates (e : Nat → Nat → Bool) (C : (Nat → Bool) → Prop) : Prop :=
  (∀ i, C (e i)) ∧ ∀ L, C L → ∃ i, e i = L

/-- `L` is decidable with one query to `u` followed by a Boolean post-processing. -/
def OneQuery (u : Nat → Nat → Bool) (L : Nat → Bool) : Prop :=
  ∃ a : Nat → Nat, ∃ g : Bool → Bool, ∀ x, L x = g (u (a x) x)

/--
Abstract time hierarchy: if `e` enumerates `C` and `u` simulates `e`, the
diagonal `x ↦ !(u x x)` is decidable with one query to `u` and is not in `C`.
-/
theorem hierarchy_abstract (e u : Nat → Nat → Bool) (C : (Nat → Bool) → Prop)
    (hu : ∀ i x, u i x = e i x) (hC : Enumerates e C) :
    OneQuery u (fun x => !(u x x)) ∧ ¬ C (fun x => !(u x x)) := by
  refine ⟨⟨fun x => x, fun b => !b, fun x => rfl⟩, fun hD => ?_⟩
  obtain ⟨i, hi⟩ := hC.2 _ hD
  have h1 : e i i = !(u i i) := congrFun hi i
  rw [hu] at h1
  rcases Bool.eq_false_or_eq_true (e i i) with hb | hb <;> simp [hb] at h1

/-- The hierarchy is strict: `C` is contained in, and different from, the one-query class. -/
theorem hierarchy_strict (e u : Nat → Nat → Bool) (C : (Nat → Bool) → Prop)
    (hu : ∀ i x, u i x = e i x) (hC : Enumerates e C) :
    (∀ L, C L → OneQuery u L) ∧ ∃ L, OneQuery u L ∧ ¬ C L := by
  refine ⟨fun L hL => ?_, _, hierarchy_abstract e u C hu hC⟩
  obtain ⟨i, hi⟩ := hC.2 L hL
  exact ⟨fun _ => i, fun b => b, fun x => by rw [← hi, hu]⟩

/-! ## Oracle worlds and relativization -/

/-- An oracle world. -/
abbrev World := Nat → Bool

/-- A statement about oracle worlds relativizes if it holds in every world. -/
def Relativizes (S : World → Prop) : Prop := ∀ O, S O

/-- A statement that fails in some world has no relativizing proof. -/
theorem no_relativizing_proof (S : World → Prop) (h : ∃ O, ¬ S O) : ¬ Relativizes S := by
  intro hS
  obtain ⟨O, hO⟩ := h
  exact hO (hS O)

/--
If `S` fails in world `A` and holds in world `B` (the BGS situation for
`S O := P^O ≠ NP^O`), then neither `S` nor `¬ S` has a relativizing proof.
-/
theorem neither_relativizes (S : World → Prop) (hA : ∃ A, ¬ S A) (hB : ∃ B, S B) :
    ¬ Relativizes S ∧ ¬ Relativizes (fun O => ¬ S O) := by
  refine ⟨no_relativizing_proof S hA, fun h => ?_⟩
  obtain ⟨B, hB⟩ := hB
  exact h B hB

/-- The diagonal argument works for every oracle-extended enumeration. -/
theorem diag_relativizes (eO : World → Nat → Nat → Bool) :
    Relativizes (fun O => ∀ i, diag (eO O) ≠ eO O i) :=
  fun O i => diag_ne (eO O) i

/-- The hierarchy argument works in every oracle world. -/
theorem hierarchy_relativizes (eO uO : World → Nat → Nat → Bool)
    (CO : World → (Nat → Bool) → Prop)
    (hu : ∀ O i x, uO O i x = eO O i x) (hC : ∀ O, Enumerates (eO O) (CO O)) :
    Relativizes (fun O => OneQuery (uO O) (fun x => !(uO O x x)) ∧
      ¬ CO O (fun x => !(uO O x x))) :=
  fun O => hierarchy_abstract (eO O) (uO O) (CO O) (hu O) (hC O)

/-- A proof technique: the set of world-statements it can establish. -/
def Technique := (World → Prop) → Prop

/-- A technique relativizes if everything it proves holds in every world. -/
def Relativizing (T : Technique) : Prop := ∀ S, T S → Relativizes S

/--
Pure diagonalization: statements that are, world by world, the diagonal
conclusion or the hierarchy conclusion for oracle-extended enumerations.
-/
def DiagTech : Technique := fun S =>
  (∃ eO : World → Nat → Nat → Bool, ∀ O, S O ↔ ∀ i, diag (eO O) ≠ eO O i) ∨
  (∃ (eO uO : World → Nat → Nat → Bool) (CO : World → (Nat → Bool) → Prop),
    (∀ O i x, uO O i x = eO O i x) ∧ (∀ O, Enumerates (eO O) (CO O)) ∧
    ∀ O, S O ↔ (OneQuery (uO O) (fun x => !(uO O x x)) ∧ ¬ CO O (fun x => !(uO O x x))))

/-- Pure diagonalization is a relativizing technique. -/
theorem diagTech_relativizing : Relativizing DiagTech := by
  intro S hS O
  rcases hS with ⟨eO, h⟩ | ⟨eO, uO, CO, hu, hC, h⟩
  · exact (h O).2 (diag_relativizes eO O)
  · exact (h O).2 (hierarchy_relativizes eO uO CO hu hC O)

/-- A relativizing technique cannot prove a statement that fails in some world. -/
theorem relativizing_cannot_prove (T : Technique) (hT : Relativizing T) (S : World → Prop)
    (h : ∃ O, ¬ S O) : ¬ T S :=
  fun hS => no_relativizing_proof S h (hT S hS)

/--
Pure diagonalization cannot prove any statement that fails in some oracle
world. With BGS, this covers both `P^O ≠ NP^O` and `P^O = NP^O`.
-/
theorem diagonalization_cannot_prove (S : World → Prop) (h : ∃ O, ¬ S O) : ¬ DiagTech S :=
  relativizing_cannot_prove DiagTech diagTech_relativizing S h

/--
Open obligation (not assumed): a technique `T` that is sound for the real
world `real`, proves `S`, and does not relativize. For `S O := P^O ≠ NP^O`
and `real` the empty oracle, this is what a diagonalization-based proof of
P ≠ NP would still have to supply.
-/
def NonRelativizingIngredient (T : Technique) (real : World) (S : World → Prop) : Prop :=
  (∀ S', T S' → S' real) ∧ T S ∧ ¬ Relativizing T

/-- Any technique that proves a world-dependent statement is non-relativizing. -/
theorem ingredient_necessary (T : Technique) (S : World → Prop) (h : ∃ O, ¬ S O)
    (hT : T S) : ¬ Relativizing T :=
  fun hR => relativizing_cannot_prove T hR S h hT

/-! ## The query-complexity core of the BGS oracle -/

/-- Deterministic adaptive oracle query algorithms (decision trees). -/
inductive QT where
  | leaf : Bool → QT
  | query : Nat → QT → QT → QT

open QT

def run (O : World) : QT → Bool
  | leaf b => b
  | query q t f => if O q then run O t else run O f

/-- Worst-case number of queries. -/
def qdepth : QT → Nat
  | leaf _ => 0
  | query _ t f => max (qdepth t) (qdepth f) + 1

/-- The points queried when running on `O`. -/
def path (O : World) : QT → List Nat
  | leaf _ => []
  | query q t f => q :: (if O q then path O t else path O f)

theorem path_length (O : World) (t : QT) : (path O t).length ≤ qdepth t := by
  induction t with
  | leaf _ => simp [path, qdepth]
  | query q t f iht ihf =>
    simp only [path, qdepth, List.length_cons]
    rcases Bool.eq_false_or_eq_true (O q) with h | h <;>
      simp only [h, reduceIte, Bool.false_eq_true] <;> omega

/-- Oracles agreeing on the queried points give the same answer. -/
theorem run_agree (O O' : World) (t : QT) (h : ∀ q, q ∈ path O t → O' q = O q) :
    run O' t = run O t := by
  induction t with
  | leaf _ => rfl
  | query q t f iht ihf =>
    have hq : O' q = O q := h q (by simp [path])
    simp only [run, hq]
    rcases Bool.eq_false_or_eq_true (O q) with hb | hb
    · simp only [hb, reduceIte]
      exact iht fun p hp => h p (by simp [path, hb, hp])
    · simp only [hb, reduceIte, Bool.false_eq_true]
      exact ihf fun p hp => h p (by simp [path, hb, hp])

/-- Bounded existential: `anyB p m = p 0 ∨ ⋯ ∨ p (m − 1)`. -/
def anyB (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | m + 1 => anyB p m || p m

theorem anyB_iff (p : Nat → Bool) (m : Nat) : anyB p m = true ↔ ∃ y, y < m ∧ p y = true := by
  induction m with
  | zero => simp [anyB]
  | succ m ih =>
    simp only [anyB, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨y, hy, hp⟩ | hp)
      · exact ⟨y, by omega, hp⟩
      · exact ⟨m, by omega, hp⟩
    · rintro ⟨y, hy, hp⟩
      by_cases hym : y = m
      · exact Or.inr (hym ▸ hp)
      · exact Or.inl ⟨y, by omega, hp⟩

/-- The BGS test language: some string of length `n` (coded as `2^n + y`, `y < 2^n`) is in `O`. -/
def testLang (O : World) (n : Nat) : Bool := anyB (fun y => O (2 ^ n + y)) (2 ^ n)

/-- Membership in the test language is verified by one certificate query (the NP side). -/
theorem testLang_one_certificate (O : World) (n : Nat) :
    testLang O n = true ↔ ∃ y, y < 2 ^ n ∧ O (2 ^ n + y) = true :=
  anyB_iff _ _

/-- A list shorter than `m` misses some point of `a, a+1, …, a+m−1`. -/
theorem exists_unqueried (a : Nat) : ∀ (m : Nat) (l : List Nat), l.length < m →
    ∃ y, y < m ∧ a + y ∉ l
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, l, h => by
    by_cases hm : a + m ∈ l
    · have hlen : (l.erase (a + m)).length < m := by
        have := List.length_pos_of_mem hm; rw [List.length_erase_of_mem hm]; omega
      obtain ⟨y, hy, hny⟩ := exists_unqueried a m (l.erase (a + m)) hlen
      refine ⟨y, by omega, fun hin => hny ?_⟩
      exact (List.mem_erase_of_ne (by omega)).2 hin
    · exact ⟨m, by omega, hm⟩

/--
Adversary theorem: every deterministic query algorithm with fewer than `2^n`
queries gets the test language wrong at length `n` for some oracle.
-/
theorem oracle_adversary (n : Nat) (t : QT) (ht : qdepth t < 2 ^ n) :
    ∃ O : World, run O t ≠ testLang O n := by
  let O0 : World := fun _ => false
  have h0 : testLang O0 n = false := by
    rcases Bool.eq_false_or_eq_true (testLang O0 n) with h | h
    · obtain ⟨y, _, hy⟩ := (testLang_one_certificate O0 n).1 h
      exact absurd hy (by simp [O0])
    · exact h
  rcases Bool.eq_false_or_eq_true (run O0 t) with h | h
  · exact ⟨O0, by rw [h, h0]; decide⟩
  · have hl : (path O0 t).length < 2 ^ n := Nat.lt_of_le_of_lt (path_length O0 t) ht
    obtain ⟨y, hy, hny⟩ := exists_unqueried (2 ^ n) (2 ^ n) (path O0 t) hl
    let O1 : World := fun z => z == 2 ^ n + y
    have hagree : ∀ q, q ∈ path O0 t → O1 q = O0 q := by
      intro q hq
      have hne : q ≠ 2 ^ n + y := fun e => hny (e ▸ hq)
      simp [O1, O0, hne]
    have h1 : testLang O1 n = true :=
      (testLang_one_certificate O1 n).2 ⟨y, hy, by simp [O1]⟩
    exact ⟨O1, by rw [run_agree O0 O1 t hagree, h, h1]; decide⟩

end Issue532.Idea16
