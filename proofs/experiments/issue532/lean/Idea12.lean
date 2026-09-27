import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 12: reduction verification

Many-one reductions `f : α → β` from `L : α → Bool` to `M : β → Bool`
(`IsReduction f L M := ∀ x, L x = M (f x)`), first without resources and then
in the repository's shared machine model
(`proofs/experiments/issue532/lean/Machines.lean`), where a reduction is
`PolyReduces L L'`: a finite-table machine computes the map within a
polynomial number of `Run` steps (`Computes m f p`).

Proved for all types, languages and maps (no cost):

* `reduction_id`, `reduction_comp`, `reduction_complement`: reductions form a
  preorder and commute with complement.
* `const_reduction_iff`, `const_not_reduction`: a const (single-valued) map reduces `L`
  exactly when `L` is const (single-valued), so it never reduces a nontrivial language.
* `trivial_target`, `nontrivial_target`: a reduction into a trivial language
  forces the source to be trivial.
* `decider_transfer`: a decider for `M` on the image of `f` yields a decider
  for `L`.
* `yes_preserving_not_sufficient`: for every nontrivial `L`, a map sending all
  yes-instances to yes-instances need not be a reduction.
* `reduces_to_any_nontrivial`: every `L` reduces to every nontrivial `M` if the
  reduction may be as expensive as deciding `L`.

Proved in the machine model:

* `polyReduces_refl`, `polyReduces_trans` (via `computes_comp`): machine
  reductions form a preorder; the composite machine is the concatenated table
  `appendMachine m m'`.
* `polyReduces_complement`: machine reductions commute with complement.
* `poly_decider_transfer` (the shared `inP_of_reduces`), `hardness_transfer`,
  `sat_hardness_transfer`: `InP` pulls back and non-membership in P pushes
  forward along `PolyReduces`; `diag_hardness_transfer` shows the hypothesis
  `¬ InP L` is satisfiable (by the shared diagonal language `Diag`).
* `reduction_cost_essential`: `Diag` reduces to the nontrivial language
  `firstBit` by an unrestricted map, but not by any `PolyReduces`; so the cost
  bound on reductions is essential.
* `sat_reduction_route_iff`, `pEqualsNP_of_sat_reduction_route`: "reduce SAT
  to something in P" is exactly `InP SAT`; it gives P = NP only under the named
  hypothesis `SATHard` (Cook–Levin, not mechanised here).

The earlier abstract cost model, in which an algorithm carries a declared
`time` field, is kept as a schema (`Algo`, `PolyBoundedFor`,
`PolyDeciderFor`, `PolyReductionFor` and the theorems with suffix `_for`).
`polyDeciderFor_every` shows that the schema alone is vacuous (every language
has a "polynomial decider" with declared time `0`), and
`polyDeciderFor_of_inP` instantiates it with the machine step count.

Verdict: reductions are the correct tool for transferring algorithms and
hardness, but they are insufficient alone: they move the question between
problems and never answer it. Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea12

open Complexity Issue532.Machines

variable {α β γ : Type}

/-- `f` is a many-one reduction from `L` to `M`. -/
def IsReduction (f : α → β) (L : α → Bool) (M : β → Bool) : Prop := ∀ x, L x = M (f x)

/-- `L` has a yes-instance and a no-instance. -/
def Nontrivial (L : α → Bool) : Prop := ∃ a b, L a = true ∧ L b = false

theorem reduction_id (L : α → Bool) : IsReduction id L L := fun _ => rfl

/-- Reductions compose. -/
theorem reduction_comp (f : α → β) (g : β → γ) (L : α → Bool) (M : β → Bool) (N : γ → Bool)
    (hf : IsReduction f L M) (hg : IsReduction g M N) : IsReduction (fun x => g (f x)) L N :=
  fun x => (hf x).trans (hg (f x))

/-- A reduction also reduces the complements. -/
theorem reduction_complement (f : α → β) (L : α → Bool) (M : β → Bool) (h : IsReduction f L M) :
    IsReduction f (fun x => !L x) (fun y => !M y) := by
  intro x; simp only [h x]

/-- A const map is a reduction iff `L` is const with value `M c`. -/
theorem const_reduction_iff (L : α → Bool) (M : β → Bool) (c : β) :
    IsReduction (fun _ : α => c) L M ↔ ∀ x, L x = M c := Iff.rfl

/-- A const map never reduces a nontrivial language. -/
theorem const_not_reduction (L : α → Bool) (M : β → Bool) (hL : Nontrivial L) (c : β) :
    ¬ IsReduction (fun _ : α => c) L M := by
  intro h
  obtain ⟨a, b, ha, hb⟩ := hL
  have h1 := h a
  have h2 := h b
  simp only at h1 h2
  rw [ha] at h1; rw [hb] at h2
  rw [← h1] at h2
  exact Bool.noConfusion h2

/-- A reduction into a const language forces the source to be const. -/
theorem trivial_target (f : α → β) (L : α → Bool) (M : β → Bool) (b : Bool)
    (hM : ∀ y, M y = b) (h : IsReduction f L M) : ∀ x, L x = b :=
  fun x => (h x).trans (hM (f x))

/-- Reductions preserve nontriviality: the target of a reduction from a nontrivial language is nontrivial. -/
theorem nontrivial_target (f : α → β) (L : α → Bool) (M : β → Bool)
    (h : IsReduction f L M) (hL : Nontrivial L) : Nontrivial M := by
  obtain ⟨a, b, ha, hb⟩ := hL
  exact ⟨f a, f b, (h a).symm.trans ha, (h b).symm.trans hb⟩

/-- A decider for `M` that is correct on the image of `f` gives a decider for `L`. -/
theorem decider_transfer (f : α → β) (L : α → Bool) (M : β → Bool) (P : β → Prop)
    (hP : ∀ x, P (f x)) (g : β → Bool) (hg : ∀ y, P y → g y = M y) (h : IsReduction f L M) :
    ∀ x, g (f x) = L x :=
  fun x => (hg (f x) (hP x)).trans (h x).symm

/--
One-directional maps are not reductions: for every nontrivial `L` and every
yes-instance `y` of `M`, the const map to `y` sends yes to yes but is not a
reduction.
-/
theorem yes_preserving_not_sufficient (L : α → Bool) (M : β → Bool) (hL : Nontrivial L)
    (y : β) (hy : M y = true) :
    (∀ x, L x = true → M ((fun _ : α => y) x) = true) ∧ ¬ IsReduction (fun _ : α => y) L M :=
  ⟨fun _ _ => hy, const_not_reduction L M hL y⟩

/--
Every language reduces to every nontrivial language when the reduction is
allowed to decide `L` itself. Hence a reduction *to* a hard problem is no
evidence of hardness, and cost bounds on reductions are essential.
-/
theorem reduces_to_any_nontrivial (L : α → Bool) (M : β → Bool) (hM : Nontrivial M) :
    ∃ f : α → β, IsReduction f L M := by
  obtain ⟨a, b, ha, hb⟩ := hM
  refine ⟨fun x => if L x then a else b, fun x => ?_⟩
  cases hx : L x
  · simp [hx, hb]
  · simp [hx, ha]

/-! ### Abstract cost schema

A schema, not a statement about the machine model: the running time is a
declared field of `Algo`, so nothing ties it to an actual computation.
`polyDeciderFor_every` makes this explicit. -/

/-- Schema: an algorithm given by its input/output behaviour and a declared
running time on each input. -/
structure Algo (α β : Type) where
  run : α → β
  time : α → Nat

/-- Schema: `t` is bounded by `c · (sz x + 1)^d`. -/
def PolyBoundedFor (sz : α → Nat) (t : α → Nat) : Prop := ∃ c d, ∀ x, t x ≤ c * (sz x + 1) ^ d

/-- Schema: `L` has an `Algo` with polynomially bounded declared time. -/
def PolyDeciderFor (sz : α → Nat) (L : α → Bool) : Prop :=
  ∃ A : Algo α Bool, (∀ x, A.run x = L x) ∧ PolyBoundedFor sz A.time

/-- Schema: a reduction `Algo` that is correct, with polynomially bounded declared
time and polynomial output size. -/
def PolyReductionFor (szA : α → Nat) (szB : β → Nat) (L : α → Bool) (M : β → Bool)
    (R : Algo α β) : Prop :=
  IsReduction R.run L M ∧
    ∃ e k, ∀ x, R.time x ≤ e * (szA x + 1) ^ k ∧ szB (R.run x) ≤ e * (szA x + 1) ^ k

/-- Composing polynomial bounds, with explicit constants. -/
theorem poly_bound_compose (n a b e k c d : Nat) (ha : a ≤ e * (n + 1) ^ k)
    (hb : b ≤ c * (a + 1) ^ d) : b ≤ c * (e + 1) ^ d * (n + 1) ^ (k * d) := by
  have hpos : 1 ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) (Nat.zero_le k)
  have h1 : a + 1 ≤ (e + 1) * (n + 1) ^ k := by rw [Nat.add_mul, Nat.one_mul]; omega
  have h2 : (a + 1) ^ d ≤ ((e + 1) * (n + 1) ^ k) ^ d := Nat.pow_le_pow_left h1 d
  rw [Nat.mul_pow, ← Nat.pow_mul] at h2
  rw [Nat.mul_assoc]
  exact Nat.le_trans hb (Nat.mul_le_mul_left c h2)

/-- Summing two polynomial bounds into one. -/
theorem poly_sum_bound (n e k C d : Nat) :
    e * (n + 1) ^ k + C * (n + 1) ^ (k * d) ≤ (e + C) * (n + 1) ^ (k * d + k) := by
  have h1 : (n + 1) ^ k ≤ (n + 1) ^ (k * d + k) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ (k * d) ≤ (n + 1) ^ (k * d + k) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left e h1) (Nat.mul_le_mul_left C h2)

/-- Schema version of the transfer: deciders pull back along reductions, with
explicit constants for the composed declared time. -/
theorem poly_decider_transfer_for (szA : α → Nat) (szB : β → Nat) (L : α → Bool) (M : β → Bool)
    (R : Algo α β) (hR : PolyReductionFor szA szB L M R) (hM : PolyDeciderFor szB M) :
    PolyDeciderFor szA L := by
  obtain ⟨hred, e, k, hek⟩ := hR
  obtain ⟨A, hA, c, d, hcd⟩ := hM
  refine ⟨⟨fun x => A.run (R.run x), fun x => R.time x + A.time (R.run x)⟩, ?_, ?_⟩
  · intro x
    show A.run (R.run x) = L x
    rw [hA, hred x]
  · refine ⟨e + c * (e + 1) ^ d, k * d + k, fun x => ?_⟩
    show R.time x + A.time (R.run x) ≤ _
    have h1 := (hek x).1
    have h2 := poly_bound_compose (szA x) (szB (R.run x)) (A.time (R.run x)) e k c d (hek x).2 (hcd _)
    have h3 := poly_sum_bound (szA x) e k (c * (e + 1) ^ d) d
    omega

/-- Schema version of composition (with explicit constants). -/
theorem poly_reduction_comp_for (szA : α → Nat) (szB : β → Nat) (szC : γ → Nat)
    (L : α → Bool) (M : β → Bool) (N : γ → Bool) (R : Algo α β) (S : Algo β γ)
    (hR : PolyReductionFor szA szB L M R) (hS : PolyReductionFor szB szC M N S) :
    PolyReductionFor szA szC L N
      ⟨fun x => S.run (R.run x), fun x => R.time x + S.time (R.run x)⟩ := by
  obtain ⟨hr, e, k, hek⟩ := hR
  obtain ⟨hs, e', k', hek'⟩ := hS
  refine ⟨reduction_comp R.run S.run L M N hr hs, e + e' * (e + 1) ^ k', k * k' + k, fun x => ?_⟩
  have h3 := poly_sum_bound (szA x) e k (e' * (e + 1) ^ k') k'
  have ht := poly_bound_compose (szA x) (szB (R.run x)) (S.time (R.run x)) e k e' k' (hek x).2 (hek' _).1
  have hz := poly_bound_compose (szA x) (szB (R.run x)) (szC (S.run (R.run x))) e k e' k' (hek x).2 (hek' _).2
  have h1 := (hek x).1
  constructor
  · show R.time x + S.time (R.run x) ≤ _
    omega
  · show szC (S.run (R.run x)) ≤ _
    omega

/-- Schema version of hardness transfer. -/
theorem hardness_transfer_for (szA : α → Nat) (szB : β → Nat) (L : α → Bool) (M : β → Bool)
    (R : Algo α β) (hR : PolyReductionFor szA szB L M R) (hL : ¬ PolyDeciderFor szA L) :
    ¬ PolyDeciderFor szB M :=
  fun hM => hL (poly_decider_transfer_for szA szB L M R hR hM)

/-- The schema alone is vacuous: with declared time `0`, every language has a
"polynomial decider".  Hence the hypothesis `¬ PolyDeciderFor szA L` of
`hardness_transfer_for` is never satisfiable, and the schema must be
instantiated with a real cost model. -/
theorem polyDeciderFor_every (sz : α → Nat) (L : α → Bool) : PolyDeciderFor sz L :=
  ⟨⟨L, fun _ => 0⟩, fun _ => rfl, 0, 0, fun _ => Nat.le_refl 0⟩

/-- Instantiating the schema with the machine model: the step count of a
polynomial-time machine is a polynomially bounded time function. -/
theorem polyDeciderFor_of_inP {L : Language} (h : InP L) : PolyDeciderFor List.length L := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  refine ⟨⟨L, fun x => Classical.choose (hm x)⟩, fun _ => rfl, p.coefficient, p.degree, fun x => ?_⟩
  obtain ⟨_, ht, _⟩ := Classical.choose_spec (hm x)
  exact ht

/-! ## Reductions in the machine model -/

/-! ### Composition of machine reductions

`PolyReduces` is a preorder.  The composite reduction runs the table of the
first machine and then the shifted table of the second (`appendMachine`); the
second phase starts from the first machine's output tape, which agrees with
the second machine's initial configuration up to trailing blanks. -/

theorem reaches_trans {M : Machine} {c d e : Config} {t1 t2 : Nat}
    (h1 : Reaches M c t1 d) (h2 : Reaches M d t2 e) : Reaches M c (t1 + t2) e := by
  induction h1 with
  | refl => simpa using h2
  | next hs _ ih => rw [Nat.add_right_comm]; exact Reaches.next hs (ih h2)

/-- A partial run of the second table is a partial run of the concatenation,
with every state shifted by the length of the first table. -/
theorem reaches_append_right (first : Machine) {second : Machine} {c d : Config} {t : Nat}
    (h : Reaches second c t d) :
    Reaches (appendMachine first second) (shiftConfig first.program.length c) t
      (shiftConfig first.program.length d) := by
  induction h with
  | refl c => exact Reaches.refl _
  | @next c c' d t hs _ ih =>
    refine Reaches.next ?_ ih
    unfold step at hs ⊢
    simp only [shiftConfig]
    rw [append_instruction_right]
    cases hins : second.instruction c.state c.head with
    | halt b' => rw [hins] at hs; cases hs
    | move q w dir =>
      rw [hins] at hs
      cases hs
      exact congrArg Sum.inr (moveHead_shift c _ q w dir)

/-- Partial runs ignore trailing blanks. -/
theorem reaches_of_similar {M : Machine} {c d c' : Config} {t : Nat}
    (h : Reaches M c t d) (hs : Similar c c') : ∃ d', Reaches M c' t d' ∧ Similar d d' := by
  induction h generalizing c' with
  | refl c => exact ⟨c', Reaches.refl _, hs⟩
  | next hstep _ ih =>
    obtain ⟨e', he', hsim⟩ := (similar_step hs).2 _ hstep
    obtain ⟨d', hd', hsd⟩ := ih hsim
    exact ⟨d', Reaches.next he' hd', hsd⟩

theorem blankPad_blanks {l : Nat} {s : List Symbol} (h : BlankPad (blanks l) s) :
    ∃ l', s = blanks l' := by
  induction l generalizing s with
  | zero =>
    induction s with
    | nil => exact ⟨0, rfl⟩
    | cons b s ih =>
      obtain ⟨hb, hs⟩ := BlankPad.nil_cons h
      obtain ⟨l', hl'⟩ := ih hs
      exact ⟨l' + 1, by rw [hb, hl']; rfl⟩
  | succ l ih =>
    cases s with
    | nil => exact ⟨0, rfl⟩
    | cons b s =>
      obtain ⟨hb, hs⟩ := BlankPad.cons_cons (a := Symbol.blank) (r := blanks l) h
      obtain ⟨l', hl'⟩ := ih hs
      exact ⟨l' + 1, by rw [← hb, hl']; rfl⟩

/-- A tape holding a word followed by blanks keeps that form under
`BlankPad`. -/
theorem blankPad_word (w : Word) {l : Nat} {s : List Symbol}
    (h : BlankPad (w.map Symbol.ofBool ++ blanks l) s) :
    ∃ l', s = w.map Symbol.ofBool ++ blanks l' := by
  induction w generalizing s with
  | nil => simpa using blankPad_blanks h
  | cons a w ih =>
    cases s with
    | nil =>
      obtain ⟨ha, _⟩ := BlankPad.nil_cons (BlankPad.symm h)
      cases a <;> cases ha
    | cons b s =>
      obtain ⟨hab, hs⟩ := BlankPad.cons_cons h
      obtain ⟨l', hl'⟩ := ih hs
      exact ⟨l', by rw [List.map_cons, List.cons_append, ← hab, hl']⟩

theorem appendMachine_length (first second : Machine) :
    (appendMachine first second).program.length =
      first.program.length + second.program.length := by
  simp [appendMachine]

/-- The empty table computes the identity in zero steps. -/
theorem computes_id : Computes ⟨[]⟩ (fun x => x) ⟨0, 0⟩ := by
  intro x
  refine ⟨0, initial x, Nat.zero_le _, Reaches.refl _, ?_⟩
  cases x with
  | nil => exact ⟨rfl, rfl, 1, rfl⟩
  | cons a x => exact ⟨rfl, rfl, 0, by simp [initial, initialSymbols, blanks]⟩

/-- **Composition of computed maps** (machine construction). -/
theorem computes_comp {m m' : Machine} {f g : Word → Word} {p p' : Polynomial}
    (hm : Computes m f p) (hm' : Computes m' g p') :
    ∃ B : Polynomial, Computes (appendMachine m m') (fun x => g (f x)) B := by
  obtain ⟨q, hq⟩ := computes_output_poly hm
  obtain ⟨B, hB⟩ := compose_bound p p' q
  refine ⟨B, fun x => ?_⟩
  obtain ⟨t1, c, ht1, hr1, hs1, hl1, k, htape1⟩ := hm x
  obtain ⟨t2, d, ht2, hr2, hs2, hl2, k2, htape2⟩ := hm' (f x)
  have hsim := similar_initial (f x) c m.program.length hs1 hl1 k htape1
  obtain ⟨d', hr2', hsd⟩ := reaches_of_similar (reaches_append_right m hr2) hsim
  obtain ⟨hst, hle, hhd, hpad⟩ := hsd
  have hpad' : BlankPad (d.head :: d.right) (d.head :: d'.right) := BlankPad.cons d.head hpad
  have htape : d.head :: d.right = (g (f x)).map Symbol.ofBool ++ blanks k2 := htape2
  rw [htape] at hpad'
  obtain ⟨l', hl'⟩ := blankPad_word (g (f x)) hpad'
  refine ⟨t1 + t2, d', ?_, reaches_trans (reaches_append m' hr1) hr2', ?_, ?_, l', ?_⟩
  · have := polynomial_eval_mono p' (hq x)
    have := hB x.length
    omega
  · rw [appendMachine_length, ← hst]
    simp only [shiftConfig]
    omega
  · rw [← hle]; exact hl2
  · have hh : d.head = d'.head := hhd
    rw [← hh]; exact hl'

/-- `PolyReduces` is reflexive. -/
theorem polyReduces_refl (L : Language) : PolyReduces L L :=
  ⟨⟨[]⟩, fun x => x, ⟨0, 0⟩, computes_id, fun _ => rfl⟩

/-- **`PolyReduces` is transitive**: machine reductions compose. -/
theorem polyReduces_trans {L M N : Language} (h1 : PolyReduces L M) (h2 : PolyReduces M N) :
    PolyReduces L N := by
  obtain ⟨m, f, p, hm, hf⟩ := h1
  obtain ⟨m', g, p', hm', hg⟩ := h2
  obtain ⟨B, hB⟩ := computes_comp hm hm'
  exact ⟨appendMachine m m', fun x => g (f x), B, hB, fun x => (hf x).trans (hg (f x))⟩

/-- Machine reductions commute with complement (the same machine works). -/
theorem polyReduces_complement {L L' : Language} (h : PolyReduces L L') :
    PolyReduces (complement L) (complement L') := by
  obtain ⟨m, f, p, hm, hf⟩ := h
  exact ⟨m, f, p, hm, fun x => by simp only [complement, hf x]⟩

/-- Polynomial deciders pull back along machine reductions (the shared
`inP_of_reduces`, the machine form of the transfer). -/
theorem poly_decider_transfer {L L' : Language} (hr : PolyReduces L L') (h : InP L') : InP L :=
  inP_of_reduces hr h

/-- **Hardness transfers forward** along machine reductions. -/
theorem hardness_transfer {L L' : Language} (hr : PolyReduces L L') (hL : ¬ InP L) : ¬ InP L' :=
  fun h => hL (poly_decider_transfer hr h)

/-- SAT instance: if `SAT` is not in P, nothing that `SAT` reduces to is in P. -/
theorem sat_hardness_transfer {L' : Language} (hr : PolyReduces SAT L') (hS : ¬ InP SAT) :
    ¬ InP L' :=
  hardness_transfer hr hS

/-- The hypothesis of `hardness_transfer` is satisfiable: every target of a
machine reduction from the diagonal language is outside P. -/
theorem diag_hardness_transfer {L' : Language} (hr : PolyReduces Diag L') : ¬ InP L' :=
  hardness_transfer hr diag_not_inP

/-- A nontrivial language in P: "the first bit is `1`". -/
def firstBit : Language := fun w =>
  match w with
  | true :: _ => true
  | _ => false

/-- One row, one step: the machine answers by the scanned symbol. -/
def firstBitMachine : Machine := ⟨[[.halt false, .halt false, .halt true, .halt false]]⟩

theorem firstBit_inP : InP firstBit := by
  refine inP_of_decidesWithin (m := firstBitMachine) (p := ⟨1, 0⟩) fun x => ⟨1, firstBit x, ?_, ?_, rfl⟩
  · simp [Polynomial.eval]
  · apply Run.halt
    cases x with
    | nil => rfl
    | cons a x => cases a <;> rfl

theorem firstBit_nontrivial : Nontrivial firstBit := ⟨[true], [], rfl, rfl⟩

/-- **The cost bound is essential.** `Diag` reduces to the nontrivial
language `firstBit` by an unrestricted map (`reduces_to_any_nontrivial`), but
by no machine reduction, since `firstBit` is in P and `Diag` is not. -/
theorem reduction_cost_essential :
    (∃ f : Word → Word, IsReduction f Diag firstBit) ∧ ¬ PolyReduces Diag firstBit :=
  ⟨reduces_to_any_nontrivial Diag firstBit firstBit_nontrivial,
    fun hr => diag_hardness_transfer hr firstBit_inP⟩

/-- "Reduce SAT to something in P" is exactly `InP SAT`: reductions only move
the question. -/
theorem sat_reduction_route_iff : (∃ M : Language, PolyReduces SAT M ∧ InP M) ↔ InP SAT :=
  ⟨fun ⟨_, hr, hM⟩ => inP_of_reduces hr hM, fun h => ⟨SAT, polyReduces_refl SAT, h⟩⟩

/-- Conditional theorem: the route gives P = NP under the named hypothesis
`SATHard` (the hardness half of Cook–Levin, not mechanised here). -/
theorem pEqualsNP_of_sat_reduction_route (hard : SATHard)
    (h : ∃ M : Language, PolyReduces SAT M ∧ InP M) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (sat_reduction_route_iff.mp h)

/-- Hardness of `SAT` pushed forward: if `SAT` is NP-hard in the machine
sense and `SAT` reduces to `M`, then `M` is NP-hard. -/
theorem npHard_of_reduces {M : Language} (hard : SATHard) (hr : PolyReduces SAT M) : NPHard M :=
  fun _ hL => polyReduces_trans (hard _ hL) hr

end Issue532.Idea12
