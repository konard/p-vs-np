/-!
# Issue #532, Idea 02 — Certificate search: the black-box query lower bound

A "certificate search" route tries candidate certificates and concludes
"unsatisfiable" when the trials fail.  This file proves, for every number of
variables `n`, that any procedure which only *evaluates* the instance on
chosen points needs `2^n` evaluations in the worst case, even adaptively.

Main results (core Lean 4, no imports):

* `pigeonhole` — a duplicate-free list contained in `Q` is no longer than `Q`.
* `exists_unqueried` — if `Q.length < 2^n`, some length-`n` vector is not in `Q`.
* `nonadaptive_indistinguishable` — for such `Q` the point indicator of an
  unqueried vector and the all-false predicate agree on every point of `Q`.
* `no_shallow_decision_tree` — **adaptive lower bound**: no decision tree of
  depth `< 2^n` decides "∃ x of length n, f x = true" for all predicates `f`.
* `linearTree_decides`, `linearTree_depth` — the bound is tight: a tree of
  depth exactly `2^n` exists.
* `pointCNF_iff`, `pointCNF_satisfiable` — every length-`n` vector `a` is the
  unique satisfying vector (among length-`n` vectors) of a CNF of `n` unit
  clauses.
* `failed_trials_do_not_certify` — for any `< 2^n` trial certificates there is
  a satisfiable CNF on variables `< n` on which every trial fails.
* `no_shallow_cnf_blackbox` — the adaptive bound for CNFs accessed only
  through evaluation: no decision tree of depth `< 2^n` decides satisfiability
  of all CNFs with variables `< n` from evaluation queries.

Verdict: refuted as a route for black-box / certificate-trial methods.  The
bound is about oracle access; a P = NP algorithm must read the formula
(white-box).  This is the relativizing core behind Baker–Gill–Solovay (1975)
and, in the quantum setting, the Bennett–Bernstein–Brassard–Vazirani (1997)
bound matched by Grover search.  None of those papers is formalized here.
-/

namespace Issue532.Idea02

/-! ## Enumeration and pigeonhole -/

def allAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allAssignments n).map (false :: ·) ++ (allAssignments n).map (true :: ·)

theorem length_allAssignments (n : Nat) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allAssignments, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]; omega

theorem mem_allAssignments_iff (n : Nat) (v : List Bool) :
    v ∈ allAssignments n ↔ v.length = n := by
  induction n generalizing v with
  | zero => cases v <;> simp [allAssignments]
  | succ n ih =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v => cases b <;> simp [allAssignments, ih]

theorem nodup_map_cons (b : Bool) (L : List (List Bool)) (h : L.Nodup) :
    (L.map (b :: ·)).Nodup := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun y hy hyx => h.1 ?_, ih h.2⟩
    have : y = x := List.cons.inj hyx |>.2
    exact this ▸ hy

theorem nodup_allAssignments (n : Nat) : (allAssignments n).Nodup := by
  induction n with
  | zero => simp [allAssignments]
  | succ n ih =>
    simp only [allAssignments]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons false _ ih, nodup_map_cons true _ ih, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨u, _, rfl⟩ := hx
    obtain ⟨w, _, rfl⟩ := hy
    exact Bool.noConfusion (List.cons.inj hxy).1

/-- Pigeonhole principle for lists. -/
theorem pigeonhole {α : Type} [DecidableEq α] (L Q : List α) (hL : L.Nodup)
    (h : ∀ x ∈ L, x ∈ Q) : L.length ≤ Q.length := by
  induction L generalizing Q with
  | nil => exact Nat.zero_le _
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    have hx : x ∈ Q := h x (List.mem_cons_self ..)
    have hsub : ∀ y ∈ L, y ∈ Q.erase x := by
      intro y hy
      have hne : y ≠ x := fun e => hL.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (h y (List.mem_cons_of_mem _ hy))
    have := ih (Q.erase x) hL.2 hsub
    rw [List.length_erase_of_mem hx] at this
    have hpos : 0 < Q.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- Fewer than `2^n` queries miss some length-`n` vector. -/
theorem exists_unqueried (n : Nat) (Q : List (List Bool)) (hQ : Q.length < 2 ^ n) :
    ∃ a, a.length = n ∧ a ∉ Q := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ x ∈ allAssignments n, x ∈ Q := by
    intro x hx
    apply Classical.byContradiction
    intro hxQ
    exact hno ⟨x, (mem_allAssignments_iff n x).mp hx, hxQ⟩
  have := pigeonhole _ Q (nodup_allAssignments n) hall
  rw [length_allAssignments] at this
  omega

/-- The point indicator of `a`. -/
def indicator (a : List Bool) (v : List Bool) : Bool := decide (v = a)

/-- Non-adaptive version: the indicator of an unqueried vector looks exactly
like the all-false predicate on every queried point. -/
theorem nonadaptive_indistinguishable (n : Nat) (Q : List (List Bool))
    (hQ : Q.length < 2 ^ n) :
    ∃ a, a.length = n ∧ (∃ x, x.length = n ∧ indicator a x = true) ∧
      ∀ v ∈ Q, indicator a v = (fun _ => false) v := by
  obtain ⟨a, ha, haQ⟩ := exists_unqueried n Q hQ
  refine ⟨a, ha, ⟨a, ha, by simp [indicator]⟩, fun v hv => ?_⟩
  have : v ≠ a := fun e => haQ (e ▸ hv)
  simp [indicator, this]

/-! ## Adaptive decision trees -/

/-- A deterministic adaptive query procedure: `query v t₀ t₁` evaluates the
black box at `v` and continues with `t₀` on `false`, `t₁` on `true`. -/
inductive DTree where
  | leaf (answer : Bool)
  | query (v : List Bool) (ifFalse ifTrue : DTree)

def DTree.eval (f : List Bool → Bool) : DTree → Bool
  | .leaf b => b
  | .query v t₀ t₁ => if f v then t₁.eval f else t₀.eval f

/-- Worst-case number of queries. -/
def DTree.depth : DTree → Nat
  | .leaf _ => 0
  | .query _ t₀ t₁ => 1 + max t₀.depth t₁.depth

/-- Points queried along the path where every answer is `false`. -/
def DTree.falsePath : DTree → List (List Bool)
  | .leaf _ => []
  | .query v t₀ _ => v :: t₀.falsePath

theorem falsePath_length_le (t : DTree) : t.falsePath.length ≤ t.depth := by
  induction t with
  | leaf b => exact Nat.le_refl 0
  | query v t₀ t₁ ih₀ _ =>
    simp only [DTree.falsePath, DTree.depth, List.length_cons]
    have := Nat.le_max_left t₀.depth t₁.depth
    omega

/-- Two predicates that are `false` on the all-false path get the same answer. -/
theorem eval_eq_of_false_on_path (t : DTree) (f g : List Bool → Bool)
    (hf : ∀ v ∈ t.falsePath, f v = false) (hg : ∀ v ∈ t.falsePath, g v = false) :
    t.eval f = t.eval g := by
  induction t with
  | leaf b => rfl
  | query v t₀ t₁ ih₀ _ =>
    simp only [DTree.falsePath] at hf hg
    simp only [DTree.eval]
    rw [hf v (List.mem_cons_self ..), hg v (List.mem_cons_self ..)]
    exact ih₀ (fun w hw => hf w (List.mem_cons_of_mem _ hw))
      (fun w hw => hg w (List.mem_cons_of_mem _ hw))

/-- `t` solves unstructured search over length-`n` vectors. -/
def DecidesSearch (n : Nat) (t : DTree) : Prop :=
  ∀ f : List Bool → Bool, t.eval f = true ↔ ∃ x, x.length = n ∧ f x = true

/-- **Adaptive black-box lower bound.**  No decision tree of depth `< 2^n`
decides whether a predicate has a length-`n` witness. -/
theorem no_shallow_decision_tree (n : Nat) (t : DTree) (hdepth : t.depth < 2 ^ n) :
    ¬ DecidesSearch n t := by
  intro hdec
  have hlen : t.falsePath.length < 2 ^ n :=
    Nat.lt_of_le_of_lt (falsePath_length_le t) hdepth
  obtain ⟨a, ha, haQ⟩ := exists_unqueried n t.falsePath hlen
  have hsame : t.eval (indicator a) = t.eval (fun _ => false) := by
    apply eval_eq_of_false_on_path
    · intro v hv
      have : v ≠ a := fun e => haQ (e ▸ hv)
      simp [indicator, this]
    · intro _ _; rfl
  have h1 : t.eval (indicator a) = true := (hdec (indicator a)).mpr ⟨a, ha, by simp [indicator]⟩
  have h0 : t.eval (fun _ => false) = true := hsame ▸ h1
  obtain ⟨x, _, hx⟩ := (hdec (fun _ => false)).mp h0
  exact Bool.noConfusion hx

/-- Query the listed points one after another. -/
def linearTree : List (List Bool) → DTree
  | [] => .leaf false
  | v :: vs => .query v (linearTree vs) (.leaf true)

theorem linearTree_depth_eq (L : List (List Bool)) : (linearTree L).depth = L.length := by
  induction L with
  | nil => rfl
  | cons v L ih => simp only [linearTree, DTree.depth, ih, List.length_cons]; omega

theorem linearTree_eval (L : List (List Bool)) (f : List Bool → Bool) :
    (linearTree L).eval f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [linearTree, DTree.eval]
  | cons v L ih =>
    simp only [linearTree, DTree.eval]
    cases hv : f v
    · simp only [ih, List.mem_cons, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, Or.inr hx, hfx⟩
      · rintro ⟨x, hx | hx, hfx⟩
        · subst hx; rw [hv] at hfx; exact absurd hfx (by decide)
        · exact ⟨x, hx, hfx⟩
    · simp only [↓reduceIte]
      exact ⟨fun _ => ⟨v, List.mem_cons_self .., hv⟩, fun _ => trivial⟩

/-- Tightness: the tree querying all `2^n` vectors decides search. -/
theorem linearTree_decides (n : Nat) : DecidesSearch n (linearTree (allAssignments n)) := by
  intro f
  rw [linearTree_eval]
  constructor
  · rintro ⟨x, hx, hfx⟩; exact ⟨x, (mem_allAssignments_iff n x).mp hx, hfx⟩
  · rintro ⟨x, hx, hfx⟩; exact ⟨x, (mem_allAssignments_iff n x).mpr hx, hfx⟩

theorem linearTree_depth (n : Nat) : (linearTree (allAssignments n)).depth = 2 ^ n := by
  rw [linearTree_depth_eq, length_allAssignments]

/-! ## CNFs as black boxes -/

structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool := a l.var == l.pos

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: c => evalLit a l || evalClause a c

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | c :: φ => evalClause a c && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a : Assignment, evalCNF a φ = true

def VarsBelow (n : Nat) (φ : CNF) : Prop := ∀ c ∈ φ, ∀ l ∈ c, l.var < n

def toAssign : List Bool → Assignment
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v, i + 1 => toAssign v i

def prefixOf (a : Assignment) : Nat → List Bool
  | 0 => []
  | n + 1 => a 0 :: prefixOf (fun i => a (i + 1)) n

theorem length_prefixOf (a : Assignment) (n : Nat) : (prefixOf a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [prefixOf, ih]

theorem toAssign_prefixOf (a : Assignment) (n i : Nat) (h : i < n) :
    toAssign (prefixOf a n) i = a i := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => a (j + 1)) i (by omega)

theorem evalClause_congr (a b : Assignment) (n : Nat) (c : Clause)
    (hab : ∀ i, i < n → a i = b i) (hc : ∀ l ∈ c, l.var < n) :
    evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [evalClause, evalLit]
    rw [hab l.var (hc l (List.mem_cons_self ..)),
      ih (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl'))]

theorem evalCNF_congr (a b : Assignment) (n : Nat) (φ : CNF)
    (hab : ∀ i, i < n → a i = b i) (hφ : VarsBelow n φ) :
    evalCNF a φ = evalCNF b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [evalCNF]
    rw [evalClause_congr a b n c hab (hφ c (List.mem_cons_self ..)),
      ih (fun c' hc' => hφ c' (List.mem_cons_of_mem _ hc'))]

def shiftClause : Clause → Clause
  | [] => []
  | l :: c => ⟨l.var + 1, l.pos⟩ :: shiftClause c

def shiftCNF : CNF → CNF
  | [] => []
  | c :: φ => shiftClause c :: shiftCNF φ

theorem evalClause_shift (a : Assignment) (c : Clause) :
    evalClause a (shiftClause c) = evalClause (fun i => a (i + 1)) c := by
  induction c with
  | nil => rfl
  | cons l c ih => simp only [shiftClause, evalClause, evalLit, ih]

theorem evalCNF_shift (a : Assignment) (φ : CNF) :
    evalCNF a (shiftCNF φ) = evalCNF (fun i => a (i + 1)) φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp only [shiftCNF, evalCNF, evalClause_shift, ih]

/-- The CNF `⋀_i (x_i = a_i)`: one unit clause per bit of `a`. -/
def pointCNF : List Bool → CNF
  | [] => []
  | b :: a => [⟨0, b⟩] :: shiftCNF (pointCNF a)

theorem shiftCNF_varsBelow (n : Nat) (φ : CNF) (h : VarsBelow n φ) :
    VarsBelow (n + 1) (shiftCNF φ) := by
  induction φ with
  | nil => intro c hc; cases hc
  | cons c φ ih =>
    intro c' hc' l hl
    simp only [shiftCNF, List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · have hc : ∀ l ∈ c, l.var < n := h c (List.mem_cons_self ..)
      clear h ih
      induction c with
      | nil => cases hl
      | cons l₀ c ihc =>
        simp only [shiftClause, List.mem_cons] at hl
        rcases hl with rfl | hl
        · have := hc l₀ (List.mem_cons_self ..); simp only; omega
        · exact ihc hl (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl'))
    · exact ih (fun c'' hc'' => h c'' (List.mem_cons_of_mem _ hc'')) c' hc' l hl

theorem pointCNF_varsBelow (a : List Bool) : VarsBelow a.length (pointCNF a) := by
  induction a with
  | nil => intro c hc; cases hc
  | cons b a ih =>
    intro c hc l hl
    simp only [pointCNF, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl; simp
    · exact shiftCNF_varsBelow _ _ ih c hc l hl

/-- Among vectors of length `a.length`, `pointCNF a` is satisfied exactly by `a`. -/
theorem pointCNF_iff (a v : List Bool) (h : v.length = a.length) :
    evalCNF (toAssign v) (pointCNF a) = true ↔ v = a := by
  induction a generalizing v with
  | nil =>
    cases v with
    | nil => simp [pointCNF, evalCNF]
    | cons _ _ => simp at h
  | cons b a ih =>
    cases v with
    | nil => simp at h
    | cons c v =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [pointCNF, evalCNF, evalClause, evalLit, Bool.or_false, evalCNF_shift,
        Bool.and_eq_true, beq_iff_eq, List.cons.injEq]
      have : (fun i => toAssign (c :: v) (i + 1)) = toAssign v := rfl
      rw [this, ih v h]
      rfl

theorem pointCNF_satisfiable (a : List Bool) : Satisfiable (pointCNF a) :=
  ⟨toAssign a, (pointCNF_iff a a rfl).mpr rfl⟩

/-- Failed trials do not certify unsatisfiability: for any `< 2^n` trial
certificates there is a satisfiable CNF with variables `< n` rejecting all
of them. -/
theorem failed_trials_do_not_certify (n : Nat) (Q : List (List Bool))
    (hQ : Q.length < 2 ^ n) :
    ∃ φ : CNF, VarsBelow n φ ∧ Satisfiable φ ∧ ∀ v ∈ Q, evalCNF (toAssign v) φ = false := by
  let norm : List Bool → List Bool := fun v => prefixOf (toAssign v) n
  have hlen : (Q.map norm).length < 2 ^ n := by rw [List.length_map]; exact hQ
  obtain ⟨a, ha, haQ⟩ := exists_unqueried n (Q.map norm) hlen
  refine ⟨pointCNF a, ha ▸ pointCNF_varsBelow a, pointCNF_satisfiable a, fun v hv => ?_⟩
  have hcongr : evalCNF (toAssign v) (pointCNF a) =
      evalCNF (toAssign (norm v)) (pointCNF a) :=
    evalCNF_congr _ _ n _ (fun i hi => (toAssign_prefixOf _ n i hi).symm)
      (ha ▸ pointCNF_varsBelow a)
  rw [hcongr]
  cases he : evalCNF (toAssign (norm v)) (pointCNF a) with
  | false => rfl
  | true =>
    have := (pointCNF_iff a (norm v) (by rw [ha]; exact length_prefixOf _ n)).mp he
    exact absurd (this ▸ List.mem_map_of_mem hv) haQ

/-- The evaluation black box of a CNF. -/
def oracle (φ : CNF) : List Bool → Bool := fun v => evalCNF (toAssign v) φ

/-- **Adaptive lower bound for CNFs as black boxes.** -/
theorem no_shallow_cnf_blackbox (n : Nat) (t : DTree) (hdepth : t.depth < 2 ^ n) :
    ¬ (∀ φ : CNF, VarsBelow n φ → (t.eval (oracle φ) = true ↔ Satisfiable φ)) := by
  intro hdec
  have hlen : t.falsePath.length < 2 ^ n :=
    Nat.lt_of_le_of_lt (falsePath_length_le t) hdepth
  obtain ⟨φ, hφ, hsat, hfalse⟩ := failed_trials_do_not_certify n t.falsePath hlen
  have hempty : VarsBelow n [[]] := by
    intro c hc l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; cases hl
  have hsame : t.eval (oracle φ) = t.eval (oracle [[]]) :=
    eval_eq_of_false_on_path t _ _ hfalse (fun _ _ => rfl)
  have h1 : t.eval (oracle φ) = true := (hdec φ hφ).mpr hsat
  have h0 : t.eval (oracle [[]]) = true := hsame ▸ h1
  obtain ⟨a, ha⟩ := (hdec [[]] hempty).mp h0
  simp [evalCNF, evalClause] at ha

end Issue532.Idea02
