import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 29: reduction chains and polynomial composition

**Verdict: correct tool, insufficient alone (general theorem proved).**

Polynomial-time many-one (Karp) reductions compose.  In the repository's
shared machine model (`proofs/experiments/issue532/lean/Machines.lean`) a
reduction is `PolyReduces L L'`: a finite-table machine computes the map
within a polynomial number of `Run` steps.  This file proves that machine
reductions form a preorder (`polyReduces_refl`, `polyReduces_trans`, via the
concatenated table `appendMachine` in `computes_comp`), so membership in P is
inherited backwards along whole chains (`inP_of_chain`, the shared
`inP_of_reduces`) and any class closed under reductions that contains an
NP-hard language contains NP (`closed_contains_np`).

The same theorem shows why "reduce NP to P" is not a shortcut.  The open
obligation of that route, stated in the machine model, is

  `SATReducesToP : Prop := ∃ L', PolyReduces SAT L' ∧ InP L'`,

and `satReducesToP_iff_inP_sat` proves it is *equivalent* to `InP SAT`.  It
yields P = NP only under the named hypothesis `SATHard` (the hardness half of
Cook–Levin, not mechanised here): `pEqualsNP_of_satReducesToP`;
`satReducesToP_iff_pEqualsNP` needs `CookLevin`.  Non-vacuity:
`not_forall_reducesToP` shows that not every language reduces to P.  Nothing
here decides P vs NP.

The explicit polynomials `Poly` (`eval n = coefficient * (n + 1) ^ degree`,
the same shape as `Complexity.Polynomial`, see `Poly.eval_toPolynomial`) are
closed under addition and substitution.  The earlier abstract model, in which
a map carries a declared cost function, is kept as a schema (`PolyMapFor`,
`PolyReductionFor`, `PolyDeciderFor`, `InPFor`, `ReducesToPFor`, …);
`inPFor_every` shows that the schema alone makes every language
"polynomial-time", and `inPFor_of_inP` instantiates it with the machine step
count.
-/

namespace Issue532.Idea29

open Complexity Issue532.Machines

/-! ## Explicit polynomials -/

/-- Explicit polynomial bound `coefficient * (n + 1) ^ degree`. -/
structure Poly where
  coefficient : Nat
  degree : Nat
  deriving Repr

/-- Evaluation of an explicit polynomial bound. -/
def Poly.eval (p : Poly) (n : Nat) : Nat :=
  p.coefficient * (n + 1) ^ p.degree

/-- Sum bound: coefficients add, degree is the maximum. -/
def Poly.add (p q : Poly) : Poly :=
  ⟨p.coefficient + q.coefficient, max p.degree q.degree⟩

/-- Substitution bound for `q ∘ p`. -/
def Poly.comp (p q : Poly) : Poly :=
  ⟨q.coefficient * (p.coefficient + 1) ^ q.degree, p.degree * q.degree⟩

/-- The identity-size bound `n ≤ 1 * (n + 1) ^ 1`. -/
def Poly.linear : Poly := ⟨1, 1⟩

/-- The zero bound. -/
def Poly.zero : Poly := ⟨0, 0⟩

theorem pow_pos_succ (n k : Nat) : 1 ≤ (n + 1) ^ k :=
  Nat.pow_pos (Nat.succ_pos n)

/-- Explicit polynomials are monotone in the input length. -/
theorem Poly.eval_mono (p : Poly) {m n : Nat} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  unfold Poly.eval
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ h) _)

/-- Closure under addition: `p.eval n + q.eval n ≤ (p.add q).eval n` for all `n`. -/
theorem Poly.add_bound (p q : Poly) (n : Nat) :
    p.eval n + q.eval n ≤ (p.add q).eval n := by
  unfold Poly.eval Poly.add
  simp only
  have hp : (n + 1) ^ p.degree ≤ (n + 1) ^ max p.degree q.degree :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left _ _)
  have hq : (n + 1) ^ q.degree ≤ (n + 1) ^ max p.degree q.degree :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right _ _)
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)

/-- Closure under composition: `q.eval (p.eval n) ≤ (p.comp q).eval n` for all `n`. -/
theorem Poly.comp_bound (p q : Poly) (n : Nat) :
    q.eval (p.eval n) ≤ (p.comp q).eval n := by
  unfold Poly.eval Poly.comp
  simp only
  have hX : 1 ≤ (n + 1) ^ p.degree := pow_pos_succ n p.degree
  have h1 : p.coefficient * (n + 1) ^ p.degree + 1
      ≤ (p.coefficient + 1) * (n + 1) ^ p.degree := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left hX _
  have h2 : (p.coefficient * (n + 1) ^ p.degree + 1) ^ q.degree
      ≤ ((p.coefficient + 1) * (n + 1) ^ p.degree) ^ q.degree :=
    Nat.pow_le_pow_left h1 _
  rw [Nat.mul_pow, ← Nat.pow_mul] at h2
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h2

/-- The existential form of closure under composition. -/
theorem poly_comp_exists (p q : Poly) : ∃ r : Poly, ∀ n, q.eval (p.eval n) ≤ r.eval n :=
  ⟨p.comp q, Poly.comp_bound p q⟩

/-- The existential form of closure under addition. -/
theorem poly_add_exists (p q : Poly) : ∃ r : Poly, ∀ n, p.eval n + q.eval n ≤ r.eval n :=
  ⟨p.add q, Poly.add_bound p q⟩

/-- `f` is a many-one reduction from `L` to `M`. -/
def IsReduction {α β : Type} (f : α → β) (L : α → Prop) (M : β → Prop) : Prop :=
  ∀ x, L x ↔ M (f x)

/-- Correctness of reductions composes. -/
theorem IsReduction.comp {α β γ : Type} {f : α → β} {g : β → γ}
    {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (hf : IsReduction f L M) (hg : IsReduction g M N) :
    IsReduction (g ∘ f) L N :=
  fun x => Iff.trans (hf x) (hg (f x))

/-- The identity is a reduction from a language to itself. -/
theorem IsReduction.id {α : Type} (L : α → Prop) : IsReduction (fun x => x) L L :=
  fun _ => Iff.rfl

/-- The explicit polynomial as a `Complexity.Polynomial`. -/
def Poly.toPolynomial (p : Poly) : Polynomial := ⟨p.coefficient, p.degree⟩

/-- `Poly.eval` is `Complexity.Polynomial.eval`. -/
theorem Poly.eval_toPolynomial (p : Poly) (n : Nat) : p.toPolynomial.eval n = p.eval n := rfl

/-! ## Abstract cost schema

A schema, not a statement about the machine model: a map or a decider carries
a declared cost function, so nothing ties the cost to a computation.
`inPFor_every` makes this explicit, and `inPFor_of_inP` instantiates the
schema with the machine step count. -/

/-- Schema: a map with a declared cost function and explicit polynomial bounds on
its time and on the size of its output. -/
structure PolyMapFor {α β : Type} (sa : α → Nat) (sb : β → Nat) where
  fn : α → β
  time : α → Nat
  timeBound : Poly
  sizeBound : Poly
  time_le : ∀ x, time x ≤ timeBound.eval (sa x)
  size_le : ∀ x, sb (fn x) ≤ sizeBound.eval (sa x)

/-- Running `f` then `g`: time is the sum, bounds are explicit. -/
def PolyMapFor.comp {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    (f : PolyMapFor sa sb) (g : PolyMapFor sb sc) : PolyMapFor sa sc where
  fn := fun x => g.fn (f.fn x)
  time := fun x => f.time x + g.time (f.fn x)
  timeBound := f.timeBound.add (f.sizeBound.comp g.timeBound)
  sizeBound := f.sizeBound.comp g.sizeBound
  time_le := by
    intro x
    have h1 := f.time_le x
    have h2 : g.time (f.fn x) ≤ g.timeBound.eval (f.sizeBound.eval (sa x)) :=
      Nat.le_trans (g.time_le (f.fn x)) (g.timeBound.eval_mono (f.size_le x))
    have h3 := Poly.comp_bound f.sizeBound g.timeBound (sa x)
    have h4 := Poly.add_bound f.timeBound (f.sizeBound.comp g.timeBound) (sa x)
    omega
  size_le := by
    intro x
    exact Nat.le_trans (Nat.le_trans (g.size_le (f.fn x))
      (g.sizeBound.eval_mono (f.size_le x))) (Poly.comp_bound _ _ _)

/-- The time of a composed chain of polynomially bounded maps is polynomial. -/
theorem comp_time_poly_for {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    (f : PolyMapFor sa sb) (g : PolyMapFor sb sc) :
    ∃ r : Poly, ∀ x, f.time x + g.time (f.fn x) ≤ r.eval (sa x) :=
  ⟨(f.comp g).timeBound, (f.comp g).time_le⟩

/-- The identity map with zero cost. -/
def PolyMapFor.ident {α : Type} (sa : α → Nat) : PolyMapFor sa sa where
  fn := fun x => x
  time := fun _ => 0
  timeBound := Poly.zero
  sizeBound := Poly.linear
  time_le := fun _ => Nat.zero_le _
  size_le := by
    intro x
    unfold Poly.eval Poly.linear
    simp only [Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- Schema: a polynomially bounded reduction from `L` to `M`, with declared cost. -/
structure PolyReductionFor {α β : Type} (sa : α → Nat) (sb : β → Nat)
    (L : α → Prop) (M : β → Prop) extends PolyMapFor sa sb where
  correct : IsReduction fn L M

/-- Polynomially bounded reductions compose. -/
def PolyReductionFor.comp {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (f : PolyReductionFor sa sb L M) (g : PolyReductionFor sb sc M N) :
    PolyReductionFor sa sc L N :=
  { f.toPolyMapFor.comp g.toPolyMapFor with
    correct := fun x => Iff.trans (f.correct x) (g.correct (f.fn x)) }

/-- The composed reduction computes `g ∘ f`. -/
theorem PolyReductionFor.comp_fn {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (f : PolyReductionFor sa sb L M) (g : PolyReductionFor sb sc M N) :
    (f.comp g).fn = g.fn ∘ f.fn := rfl

/-- Schema: a decider with a declared cost function and an explicit polynomial
time bound. -/
structure PolyDeciderFor {α : Type} (sa : α → Nat) (L : α → Prop) where
  decide : α → Bool
  time : α → Nat
  bound : Poly
  correct : ∀ x, L x ↔ decide x = true
  time_le : ∀ x, time x ≤ bound.eval (sa x)

/-- Schema: the polynomial-time class relative to a size function and declared
costs. -/
def InPFor {α : Type} (sa : α → Nat) (L : α → Prop) : Prop :=
  Nonempty (PolyDeciderFor sa L)

/-- Pull a decider back along a polynomially bounded reduction. -/
def PolyDeciderFor.pullback {α β : Type} {sa : α → Nat} {sb : β → Nat}
    {L : α → Prop} {M : β → Prop}
    (r : PolyReductionFor sa sb L M) (d : PolyDeciderFor sb M) : PolyDeciderFor sa L where
  decide := fun x => d.decide (r.fn x)
  time := fun x => r.time x + d.time (r.fn x)
  bound := r.timeBound.add (r.sizeBound.comp d.bound)
  correct := fun x => Iff.trans (r.correct x) (d.correct (r.fn x))
  time_le := by
    intro x
    have h1 := r.time_le x
    have h2 : d.time (r.fn x) ≤ d.bound.eval (r.sizeBound.eval (sa x)) :=
      Nat.le_trans (d.time_le (r.fn x)) (d.bound.eval_mono (r.size_le x))
    have h3 := Poly.comp_bound r.sizeBound d.bound (sa x)
    have h4 := Poly.add_bound r.timeBound (r.sizeBound.comp d.bound) (sa x)
    omega

/-- The polynomial-time class is closed backwards under polynomial reductions. -/
theorem inPFor_of_reduction {α β : Type} {sa : α → Nat} {sb : β → Nat}
    {L : α → Prop} {M : β → Prop}
    (r : PolyReductionFor sa sb L M) (h : InPFor sb M) : InPFor sa L :=
  match h with
  | ⟨d⟩ => ⟨d.pullback r⟩

/-- Schema: a class of languages over `α` closed backwards under schema
reductions. -/
def ClosedUnderReductionsFor {α : Type} (sa : α → Nat) (C : (α → Prop) → Prop) : Prop :=
  ∀ L M, Nonempty (PolyReductionFor sa sa L M) → C M → C L

/-- `InPFor` is such a class. -/
theorem inPFor_closed {α : Type} (sa : α → Nat) : ClosedUnderReductionsFor sa (InPFor sa) :=
  fun _ _ hr hM => match hr with
    | ⟨r⟩ => inPFor_of_reduction r hM

/-- Any class closed under reductions that contains one language complete for a
family contains the whole family. -/
theorem closed_contains_family_for {α : Type} (sa : α → Nat) (C : (α → Prop) → Prop)
    (hC : ClosedUnderReductionsFor sa C) (family : (α → Prop) → Prop) (K : α → Prop)
    (hard : ∀ L, family L → Nonempty (PolyReductionFor sa sa L K)) (hK : C K) :
    ∀ L, family L → C L :=
  fun L hL => hC L K (hard L hL) hK

/-- Schema: "reduce `L` to a language in `InPFor`", over declared costs. -/
def ReducesToPFor {α : Type} (sa : α → Nat) (L : α → Prop) : Prop :=
  ∃ (β : Type) (sb : β → Nat) (M : β → Prop),
    Nonempty (PolyReductionFor sa sb L M) ∧ InPFor sb M

/-- Schema version: reducing `L` to some polynomial-time language is equivalent
to `L` itself being polynomial-time. -/
theorem reducesToPFor_iff_inPFor {α : Type} (sa : α → Nat) (L : α → Prop) :
    ReducesToPFor sa L ↔ InPFor sa L := by
  constructor
  · intro ⟨_, _, _, ⟨r⟩, hM⟩
    exact inPFor_of_reduction r hM
  · intro h
    exact ⟨α, sa, L, ⟨{ PolyMapFor.ident sa with correct := IsReduction.id L }⟩, h⟩

/-- The schema alone is vacuous: with declared cost `0`, every language is in
`InPFor`. -/
theorem inPFor_every {α : Type} (sa : α → Nat) (L : α → Prop) : InPFor sa L := by
  classical
  exact ⟨{ decide := fun x => decide (L x), time := fun _ => 0, bound := Poly.zero,
           correct := fun x => (decide_eq_true_iff).symm,
           time_le := fun _ => Nat.zero_le _ }⟩

/-- Instantiating the schema with the machine model: the step count of a
polynomial-time machine is a declared cost bounded by the machine's polynomial. -/
theorem inPFor_of_inP {L : Language} (h : InP L) :
    InPFor List.length (fun x => L x = true) := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  exact ⟨{ decide := L, time := fun x => Classical.choose (hm x),
           bound := ⟨p.coefficient, p.degree⟩, correct := fun _ => Iff.rfl,
           time_le := fun x => (Classical.choose_spec (hm x)).choose_spec.1 }⟩

/-! ## Reduction chains in the machine model -/

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

/-- Membership in P is inherited backwards along a two-step chain. -/
theorem inP_of_chain {L M N : Language} (h1 : PolyReduces L M) (h2 : PolyReduces M N)
    (hN : InP N) : InP L :=
  inP_of_reduces (polyReduces_trans h1 h2) hN

/-- A class of languages closed backwards under machine reductions. -/
def ClosedUnderPolyReduces (C : Language → Prop) : Prop :=
  ∀ L M, PolyReduces L M → C M → C L

/-- `InP` is closed under machine reductions. -/
theorem inP_closedUnderPolyReduces : ClosedUnderPolyReduces InP :=
  fun _ _ hr hM => inP_of_reduces hr hM

/-- NP-hardness is inherited forwards along machine reductions. -/
theorem npHard_of_reduces {K M : Language} (hK : NPHard K) (hr : PolyReduces K M) : NPHard M :=
  fun L hL => polyReduces_trans (hK L hL) hr

/-- Any class closed under machine reductions that contains an NP-hard
language contains all of NP. -/
theorem closed_contains_np {C : Language → Prop} (hC : ClosedUnderPolyReduces C)
    {K : Language} (hK : NPHard K) (hCK : C K) : ∀ L, InNP L → C L :=
  fun L hL => hC L K (hK L hL) hCK

/-- An NP-hard language in P gives P = NP. -/
theorem pEqualsNP_of_npHard_inP {K : Language} (hK : NPHard K) (hP : InP K) : PEqualsNP :=
  closed_contains_np inP_closedUnderPolyReduces hK hP

/-- "Reduce `L` to a language already in P", in the machine model. -/
def ReducesToP (L : Language) : Prop := ∃ L' : Language, PolyReduces L L' ∧ InP L'

/-- Reducing `L` to some language in P is equivalent to `L ∈ P`. -/
theorem reducesToP_iff_inP (L : Language) : ReducesToP L ↔ InP L :=
  ⟨fun ⟨_, hr, hL'⟩ => inP_of_reduces hr hL', fun h => ⟨L, polyReduces_refl L, h⟩⟩

/-- Non-vacuity: not every language reduces to a language in P (the shared
diagonal language `Diag` does not). -/
theorem not_forall_reducesToP : ¬ ∀ L : Language, ReducesToP L :=
  fun h => diag_not_inP ((reducesToP_iff_inP Diag).mp (h Diag))

/-! ## The obligation of the "reduce SAT to P" route -/

/-- **Open obligation.**  A machine reduction (`PolyReduces`) from `SAT` to
some language `L'` together with a polynomial-time machine for `L'`.  This is
the obligation of every "reduce NP to an easy problem" argument, stated in the
shared machine model; it is a `def … : Prop` and is never postulated. -/
def SATReducesToP : Prop := ∃ L' : Language, PolyReduces SAT L' ∧ InP L'

/-- The obligation is exactly as hard as the goal: it is equivalent to
`InP SAT`. -/
theorem satReducesToP_iff_inP_sat : SATReducesToP ↔ InP SAT :=
  reducesToP_iff_inP SAT

/-- Conditional theorem: under the named hypothesis `SATHard` (hardness half of
Cook–Levin, not mechanised here) the obligation gives P = NP. -/
theorem pEqualsNP_of_satReducesToP (hard : SATHard) (h : SATReducesToP) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (satReducesToP_iff_inP_sat.mp h)

/-- Under the named hypothesis `CookLevin` the obligation is exactly P = NP. -/
theorem satReducesToP_iff_pEqualsNP (hCL : CookLevin) : SATReducesToP ↔ PEqualsNP :=
  satReducesToP_iff_inP_sat.trans (inP_sat_iff hCL)

/-- Refuting the obligation would separate P from NP (given `SATInNP`). -/
theorem pNotEqualsNP_of_not_satReducesToP (mem : SATInNP) (h : ¬ SATReducesToP) :
    PNotEqualsNP :=
  fun hp => h (satReducesToP_iff_inP_sat.mpr (inP_sat_of_pEqualsNP mem hp))

/-- A chain `SAT → L₁ → L₂` ending in P discharges the obligation. -/
theorem satReducesToP_of_chain {L₁ L₂ : Language} (h1 : PolyReduces SAT L₁)
    (h2 : PolyReduces L₁ L₂) (hP : InP L₂) : SATReducesToP :=
  ⟨L₂, polyReduces_trans h1 h2, hP⟩

end Issue532.Idea29
