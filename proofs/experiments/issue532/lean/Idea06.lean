/-!
# Issue #532, Idea 06: local search and potential functions

Summary.
* Line landscapes (`trapCost`, `lineNbr`), for every scale `M ≥ 1` and every
  length `n ≥ 2`: state `0` is a strict local minimum of cost `M`, the global
  minimum is `0` at state `n`, and every improving walk that starts in
  `0, …, n−2` stays there (`line_basin`, `line_never_reaches_global`).
* SAT with cost = number of falsified clauses (`unsatCount`). For every radius
  `k`, the formula `trapCNF k` on `k+1` variables is satisfiable, yet the
  all-false assignment has cost `1` and every assignment differing from it in
  at most `k` of the variables `0..k` has cost `≥ 1`
  (`bounded_flip_not_exact`). So `k`-flip local search is not exact for any
  fixed `k`.
* Exactness in general. The full neighbourhood is exact
  (`full_neighbourhood_exact`). There is even an exact neighbourhood of size
  `1` for every CNF (`exists_size_one_exact_neighbourhood`), namely "jump to a
  best assignment". Size is therefore not the obstacle; computing the
  neighbourhood is.
* Conditional theorem (`exact_local_search_decides`,
  `localSearch_evals_le`). With any exact neighbourhood of size `≤ B`, local
  search from `a` runs at most `unsatCount a φ + 1` rounds, performs at most
  `(unsatCount a φ + 1) · B` neighbour evaluations, and its result satisfies
  `φ` iff `φ` is satisfiable.

Verdict: refuted as a route (general theorem). A neighbourhood that is exact
and efficiently computable would give a polynomial SAT decider (Idea 01's
`PolySATDecider`). Every fixed-radius flip neighbourhood fails exactness.
-/

namespace Issue532.Idea06

/-! ## CNF syntax and semantics -/

/-- A literal: variable index and polarity (`pos = true` means `x_var`). -/
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

/-- All variables of `φ` are `< n`. -/
def VarsBelow (n : Nat) (φ : CNF) : Prop := ∀ c ∈ φ, ∀ l ∈ c, l.var < n

theorem evalClause_congr (a b : Assignment) (n : Nat) (c : Clause)
    (hab : ∀ i, i < n → a i = b i) (hc : ∀ l ∈ c, l.var < n) :
    evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [evalClause, evalLit]
    rw [hab l.var (hc l (List.mem_cons_self ..)),
      ih (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl'))]

/-- Formulas with variables `< n` only look at the first `n` values. -/
theorem evalCNF_congr (a b : Assignment) (n : Nat) (φ : CNF)
    (hab : ∀ i, i < n → a i = b i) (hφ : VarsBelow n φ) :
    evalCNF a φ = evalCNF b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [evalCNF]
    rw [evalClause_congr a b n c hab (hφ c (List.mem_cons_self ..)),
      ih (fun c' hc' => hφ c' (List.mem_cons_of_mem _ hc'))]

/-! ## Enumerating all assignments -/

/-- All `2^n` bit vectors of length `n` (bit `0` is the head). -/
def allAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allAssignments n).map (false :: ·) ++ (allAssignments n).map (true :: ·)

/-- Bit vector to assignment: index `i` ↦ bit `i`, `false` beyond the end. -/
def toAssign : List Bool → Assignment
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v, i + 1 => toAssign v i

/-- The first `n` values of an assignment, as a bit vector. -/
def prefixOf (a : Assignment) : Nat → List Bool
  | 0 => []
  | n + 1 => a 0 :: prefixOf (fun i => a (i + 1)) n

/-- The enumeration has exactly `2^n` entries. -/
theorem length_allAssignments (n : Nat) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allAssignments, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]; omega

/-- The enumeration contains exactly the vectors of length `n`. -/
theorem mem_allAssignments_iff (n : Nat) (v : List Bool) :
    v ∈ allAssignments n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v => simp [allAssignments]
  | succ n ih =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v =>
      cases b <;> simp [allAssignments, ih]

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

/-- The enumeration has no repetitions: it lists `2^n` *distinct* vectors. -/
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

/-! ## Number of variables -/

def clauseBound : Clause → Nat
  | [] => 0
  | l :: c => max (l.var + 1) (clauseBound c)

/-- One more than the largest variable index (0 for variable-free formulas). -/
def numVars : CNF → Nat
  | [] => 0
  | c :: φ => max (clauseBound c) (numVars φ)

theorem lt_clauseBound (c : Clause) : ∀ l ∈ c, l.var < clauseBound c := by
  induction c with
  | nil => intro l hl; cases hl
  | cons l c ih =>
    intro l' hl'
    simp only [clauseBound]
    rcases List.mem_cons.mp hl' with h | h
    · subst h; omega
    · have := ih l' h; omega

theorem varsBelow_numVars (φ : CNF) : VarsBelow (numVars φ) φ := by
  induction φ with
  | nil => intro c hc; cases hc
  | cons c φ ih =>
    intro c' hc' l hl
    simp only [numVars]
    rcases List.mem_cons.mp hc' with h | h
    · subst h; have := lt_clauseBound c' l hl; omega
    · have := ih c' h l hl; omega


/-! ## Local minima -/

/-- `s` is a local minimum of `cost` for the neighbourhood `nbr`. -/
def IsLocalMin {α : Type} (cost : α → Nat) (nbr : α → List α) (s : α) : Prop :=
  ∀ t, t ∈ nbr s → cost s ≤ cost t

/-- A neighbourhood is exact (over the whole state space) if every local
minimum is a global minimum. -/
def ExactAll {α : Type} (cost : α → Nat) (nbr : α → List α) : Prop :=
  ∀ s, IsLocalMin cost nbr s → ∀ t, cost s ≤ cost t

/-- An improving walk: each step moves to a neighbour of strictly smaller cost. -/
inductive ImpPath {α : Type} (cost : α → Nat) (nbr : α → List α) : α → α → Prop
  | refl (s : α) : ImpPath cost nbr s s
  | step {s t u : α} : t ∈ nbr s → cost t < cost s → ImpPath cost nbr t u →
      ImpPath cost nbr s u

/-! ## The deceptive line landscape -/

/-- Neighbours of `i` on the line `0, …, n`. -/
def lineNbr (n i : Nat) : List Nat :=
  (if 0 < i then [i - 1] else []) ++ (if i < n then [i + 1] else [])

/-- Cost `M + i` everywhere except the far end `n`, which costs `0`. -/
def trapCost (M n i : Nat) : Nat := if i = n then 0 else M + i

theorem mem_lineNbr (n i t : Nat) (h : t ∈ lineNbr n i) :
    (0 < i ∧ t = i - 1) ∨ (i < n ∧ t = i + 1) := by
  unfold lineNbr at h
  rcases List.mem_append.mp h with h | h
  · by_cases hi : 0 < i
    · simp [hi] at h; omega
    · simp [hi] at h
  · by_cases hi : i < n
    · simp [hi] at h; omega
    · simp [hi] at h

/-- State `0` is a strict local minimum (for `n ≥ 2`). -/
theorem line_strict_local_min (M n : Nat) (h : 2 ≤ n) :
    ∀ t, t ∈ lineNbr n 0 → trapCost M n 0 < trapCost M n t := by
  intro t ht
  rcases mem_lineNbr n 0 t ht with ⟨h1, _⟩ | ⟨_, h2⟩
  · omega
  · subst h2
    unfold trapCost
    have h0 : ¬ (0 = n) := by omega
    have h1 : ¬ (0 + 1 = n) := by omega
    simp only [h0, h1, ↓reduceIte]
    omega

/-- State `n` is a global minimum. -/
theorem line_global_min (M n : Nat) : ∀ t, trapCost M n n ≤ trapCost M n t := by
  intro t; simp [trapCost]

/-- For `M ≥ 1` and `n ≥ 2`, state `0` is a local minimum that is not global. -/
theorem line_local_not_global (M n : Nat) (hM : 1 ≤ M) (h : 2 ≤ n) :
    IsLocalMin (trapCost M n) (lineNbr n) 0 ∧ trapCost M n n < trapCost M n 0 := by
  refine ⟨fun t ht => Nat.le_of_lt (line_strict_local_min M n h t ht), ?_⟩
  have h0 : ¬ (0 = n) := by omega
  simp only [trapCost, h0, ↓reduceIte]
  omega

/-- The basin of the false minimum: an improving walk that starts at a state
`i ≤ n − 2` never leaves `{0, …, n−2}`. -/
theorem line_basin (M n i t : Nat) (hi : i + 2 ≤ n)
    (hp : ImpPath (trapCost M n) (lineNbr n) i t) : t + 2 ≤ n := by
  induction hp with
  | refl => exact hi
  | @step s u w hmem hlt _ ih =>
    apply ih
    rcases mem_lineNbr n s u hmem with ⟨_, h2⟩ | ⟨_, h2⟩
    · omega
    · subst h2
      unfold trapCost at hlt
      have hs : ¬ (s = n) := by omega
      by_cases hu : s + 1 = n
      · omega
      · simp only [hs, hu, ↓reduceIte] at hlt; omega

/-- Improving walks from `0, …, n−2` never reach the global minimum `n`. -/
theorem line_never_reaches_global (M n i : Nat) (hi : i + 2 ≤ n) :
    ¬ ImpPath (trapCost M n) (lineNbr n) i n := by
  intro hp
  have := line_basin M n i n hi hp
  omega

/-! ## Exact neighbourhoods -/

/-- The full neighbourhood is exact. -/
theorem full_neighbourhood_exact {α : Type} (cost : α → Nat) (U : List α)
    (hU : ∀ t, t ∈ U) : ExactAll cost (fun _ => U) :=
  fun _ hs t => hs t (hU t)

/-- Jumping directly to a global minimum is an exact neighbourhood of size 1. -/
theorem singleton_exact_neighbourhood {α : Type} (cost : α → Nat) (best : α)
    (hbest : ∀ t, cost best ≤ cost t) : ExactAll cost (fun _ => [best]) :=
  fun _ hs t => Nat.le_trans (hs best (List.mem_singleton.mpr rfl)) (hbest t)

/-- Improving walks are short: their length is bounded by the start cost. -/
def Descending {α : Type} (cost : α → Nat) : List α → Prop
  | [] => True
  | [_] => True
  | s :: t :: rest => cost t < cost s ∧ Descending cost (t :: rest)

theorem descending_length_le {α : Type} (cost : α → Nat) (s : α) (rest : List α)
    (h : Descending cost (s :: rest)) : rest.length ≤ cost s := by
  induction rest generalizing s with
  | nil => exact Nat.zero_le _
  | cons t rest ih =>
    have ⟨hlt, hd⟩ := h
    have := ih t hd
    simp only [List.length_cons]
    omega

/-! ## Local search with an evaluation count -/

/-- First neighbour that improves on `s`, if any. -/
def firstImproving {α : Type} (cost : α → Nat) (s : α) : List α → Option α
  | [] => none
  | t :: ts => if cost t < cost s then some t else firstImproving cost s ts

theorem firstImproving_some {α : Type} (cost : α → Nat) (s t : α) (L : List α)
    (h : firstImproving cost s L = some t) : t ∈ L ∧ cost t < cost s := by
  induction L with
  | nil => simp [firstImproving] at h
  | cons u L ih =>
    simp only [firstImproving] at h
    split at h
    · rename_i hlt
      have : u = t := Option.some.inj h
      subst this
      exact ⟨List.mem_cons_self .., hlt⟩
    · have := ih h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem firstImproving_none {α : Type} (cost : α → Nat) (s : α) (L : List α)
    (h : firstImproving cost s L = none) : ∀ t, t ∈ L → cost s ≤ cost t := by
  induction L with
  | nil => intro t ht; cases ht
  | cons u L ih =>
    simp only [firstImproving] at h
    split at h
    · cases h
    · rename_i hlt
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · exact ih h t ht

/-- Local search: move to the first improving neighbour, at most `fuel` times. -/
def localSearch {α : Type} (cost : α → Nat) (nbr : α → List α) : Nat → α → α
  | 0, s => s
  | f + 1, s =>
    match firstImproving cost s (nbr s) with
    | none => s
    | some t => localSearch cost nbr f t

/-- Number of neighbour evaluations performed by `localSearch`. -/
def searchEvals {α : Type} (cost : α → Nat) (nbr : α → List α) : Nat → α → Nat
  | 0, _ => 0
  | f + 1, s =>
    (nbr s).length +
      match firstImproving cost s (nbr s) with
      | none => 0
      | some t => searchEvals cost nbr f t

/-- With more fuel than the start cost, local search ends at a local minimum. -/
theorem localSearch_localMin {α : Type} (cost : α → Nat) (nbr : α → List α)
    (f : Nat) (s : α) (hf : cost s < f) : IsLocalMin cost nbr (localSearch cost nbr f s) := by
  induction f generalizing s with
  | zero => omega
  | succ f ih =>
    simp only [localSearch]
    split
    · rename_i hn
      exact firstImproving_none cost s (nbr s) hn
    · rename_i t ht
      have := (firstImproving_some cost s t (nbr s) ht).2
      exact ih t (by omega)

/-- Evaluation count: at most `fuel · B` if every neighbourhood has size `≤ B`. -/
theorem localSearch_evals_le {α : Type} (cost : α → Nat) (nbr : α → List α)
    (B : Nat) (hB : ∀ s, (nbr s).length ≤ B) (f : Nat) (s : α) :
    searchEvals cost nbr f s ≤ f * B := by
  induction f generalizing s with
  | zero => simp [searchEvals]
  | succ f ih =>
    simp only [searchEvals]
    have h1 := hB s
    split
    · rw [Nat.succ_mul]; omega
    · rename_i t _
      have h2 := ih t
      rw [Nat.succ_mul]; omega

/-! ## SAT as a local search problem -/

/-- Number of clauses of `φ` falsified by `a`. -/
def unsatCount (a : Assignment) : CNF → Nat
  | [] => 0
  | c :: φ => (if evalClause a c = true then 0 else 1) + unsatCount a φ

theorem unsatCount_eq_zero_iff (a : Assignment) (φ : CNF) :
    unsatCount a φ = 0 ↔ evalCNF a φ = true := by
  induction φ with
  | nil => simp [unsatCount, evalCNF]
  | cons c φ ih =>
    simp only [unsatCount, evalCNF, Bool.and_eq_true]
    cases evalClause a c <;> simp [ih]

theorem unsatCount_congr (a b : Assignment) (n : Nat) (φ : CNF)
    (hab : ∀ i, i < n → a i = b i) (hφ : VarsBelow n φ) :
    unsatCount a φ = unsatCount b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [unsatCount]
    rw [evalClause_congr a b n c hab (hφ c (List.mem_cons_self ..)),
      ih (fun c' hc' => hφ c' (List.mem_cons_of_mem _ hc'))]

/-- Conditional theorem: with an exact neighbourhood, local search started
anywhere, with fuel `unsatCount a φ + 1`, returns an assignment that satisfies
`φ` iff `φ` is satisfiable. -/
theorem exact_local_search_decides (φ : CNF) (nbr : Assignment → List Assignment)
    (hex : ExactAll (fun a => unsatCount a φ) nbr) (a : Assignment) :
    evalCNF (localSearch (fun b => unsatCount b φ) nbr (unsatCount a φ + 1) a) φ = true
      ↔ Satisfiable φ := by
  constructor
  · intro h; exact ⟨_, h⟩
  · intro ⟨t, ht⟩
    have hloc := localSearch_localMin (fun b => unsatCount b φ) nbr
      (unsatCount a φ + 1) a (Nat.lt_succ_self _)
    have hle := hex _ hloc t
    have h0 := (unsatCount_eq_zero_iff t φ).mpr ht
    exact (unsatCount_eq_zero_iff _ φ).mp (by simp only at hle; omega)

/-- A best assignment, found by exhaustive search over `2^(numVars φ)` vectors. -/
def argminBy {α : Type} (f : α → Nat) : α → List α → α
  | o, [] => o
  | o, p :: ps => if f (argminBy f p ps) < f o then argminBy f p ps else o

theorem argminBy_le {α : Type} (f : α → Nat) (o : α) (os : List α) :
    ∀ p, p ∈ o :: os → f (argminBy f o os) ≤ f p := by
  induction os generalizing o with
  | nil =>
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    simp [argminBy]
  | cons q qs ih =>
    intro p hp
    have hq := ih q
    simp only [argminBy]
    split
    · rename_i h
      rcases List.mem_cons.mp hp with hpo | hp'
      · subst hpo; omega
      · exact hq p hp'
    · rename_i h
      rcases List.mem_cons.mp hp with hpo | hp'
      · subst hpo; exact Nat.le_refl _
      · have := hq p hp'; omega

def bestAssign (φ : CNF) : Assignment :=
  toAssign (argminBy (fun v => unsatCount (toAssign v) φ) [] (allAssignments (numVars φ)))

theorem bestAssign_min (φ : CNF) : ∀ t, unsatCount (bestAssign φ) φ ≤ unsatCount t φ := by
  intro t
  have hmem : prefixOf t (numVars φ) ∈ allAssignments (numVars φ) :=
    (mem_allAssignments_iff _ _).mpr (length_prefixOf t _)
  have h1 := argminBy_le (fun v => unsatCount (toAssign v) φ) [] (allAssignments (numVars φ))
    (prefixOf t (numVars φ)) (List.mem_cons_of_mem _ hmem)
  have h2 := unsatCount_congr (toAssign (prefixOf t (numVars φ))) t (numVars φ) φ
    (fun i hi => toAssign_prefixOf t _ i hi) (varsBelow_numVars φ)
  unfold bestAssign
  omega

/-- For every CNF there is an exact neighbourhood of size one. The size of an
exact neighbourhood is therefore no obstacle; the cost of computing it is. -/
theorem exists_size_one_exact_neighbourhood :
    ∃ N : CNF → Assignment → List Assignment,
      (∀ φ a, (N φ a).length = 1) ∧ ∀ φ, ExactAll (fun a => unsatCount a φ) (N φ) :=
  ⟨fun φ _ => [bestAssign φ], fun _ _ => rfl,
    fun φ => singleton_exact_neighbourhood _ (bestAssign φ) (bestAssign_min φ)⟩

/-! ## Fixed-radius flip neighbourhoods are not exact -/

/-- `b` differs from `a` on at most `k` of the variables `0, …, n−1`. -/
def Within (k n : Nat) (a b : Assignment) : Prop :=
  ∃ S : List Nat, S.length ≤ k ∧ ∀ i, i < n → a i ≠ b i → i ∈ S

/-- `trapCNF k` on variables `0..k`: the clause `x_0 ∨ … ∨ x_k` plus all
implications `x_i → x_j`. Only all-true satisfies it. -/
def trapCNF (k : Nat) : CNF :=
  ((List.range (k + 1)).map (fun i => (⟨i, true⟩ : Lit))) ::
    (List.range (k + 1)).flatMap (fun i =>
      (List.range (k + 1)).map (fun j => [(⟨i, false⟩ : Lit), ⟨j, true⟩]))

theorem evalClause_true_iff (a : Assignment) (c : Clause) :
    evalClause a c = true ↔ ∃ l, l ∈ c ∧ evalLit a l = true := by
  induction c with
  | nil => simp [evalClause]
  | cons l c ih => simp [evalClause, ih]

theorem evalCNF_true_iff (a : Assignment) (φ : CNF) :
    evalCNF a φ = true ↔ ∀ c, c ∈ φ → evalClause a c = true := by
  induction φ with
  | nil => simp [evalCNF]
  | cons c φ ih => simp [evalCNF, ih]

theorem mem_trap_pairs (k : Nat) (c : Clause) :
    c ∈ (List.range (k + 1)).flatMap (fun i =>
      (List.range (k + 1)).map (fun j => [(⟨i, false⟩ : Lit), ⟨j, true⟩])) ↔
    ∃ i j, i < k + 1 ∧ j < k + 1 ∧ c = [⟨i, false⟩, ⟨j, true⟩] := by
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · intro ⟨i, hi, j, hj, hc⟩; exact ⟨i, j, hi, hj, hc.symm⟩
  · intro ⟨i, j, hi, hj, hc⟩; exact ⟨i, hi, j, hj, hc.symm⟩

/-- All-true satisfies `trapCNF k`. -/
theorem trapCNF_allTrue (k : Nat) : evalCNF (fun _ => true) (trapCNF k) = true := by
  rw [evalCNF_true_iff]
  intro c hc
  rw [evalClause_true_iff]
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨⟨0, true⟩, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, rfl⟩
  · obtain ⟨i, j, _, _, rfl⟩ := (mem_trap_pairs k c).mp hc
    exact ⟨⟨j, true⟩, by simp, rfl⟩

/-- All-false falsifies exactly one clause of `trapCNF k`. -/
theorem trapCNF_allFalse_cost (k : Nat) : unsatCount (fun _ => false) (trapCNF k) = 1 := by
  have hfirst : evalClause (fun _ => false)
      ((List.range (k + 1)).map (fun i => (⟨i, true⟩ : Lit))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨l, hl, hev⟩ := (evalClause_true_iff _ _).mp h
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    simp [evalLit] at hev
  have hrest : evalCNF (fun _ => false) ((List.range (k + 1)).flatMap (fun i =>
      (List.range (k + 1)).map (fun j => [(⟨i, false⟩ : Lit), ⟨j, true⟩]))) = true := by
    rw [evalCNF_true_iff]
    intro c hc
    obtain ⟨i, j, _, _, rfl⟩ := (mem_trap_pairs k c).mp hc
    rfl
  simp only [trapCNF, unsatCount, hfirst]
  rw [(unsatCount_eq_zero_iff _ _).mpr hrest]
  rfl

/-- Every assignment within `k` flips of all-false (on variables `0..k`)
falsifies `trapCNF k`. -/
theorem trapCNF_near_allFalse (k : Nat) (b : Assignment)
    (hb : Within k (k + 1) (fun _ => false) b) : evalCNF b (trapCNF k) = false := by
  obtain ⟨S, hS, hcov⟩ := hb
  -- pigeonhole: some variable `i ≤ k` is not flipped
  have hmiss : ∃ i, i < k + 1 ∧ i ∉ S := by
    apply Classical.byContradiction
    intro hno
    have hsub : List.range (k + 1) ⊆ S := by
      intro i hi
      have hi' := List.mem_range.mp hi
      apply Classical.byContradiction
      intro hni
      exact hno ⟨i, hi', hni⟩
    have := List.Nodup.length_le_of_subset List.nodup_range hsub
    rw [List.length_range] at this
    omega
  obtain ⟨i, hi, hiS⟩ := hmiss
  have hbi : b i = false := by
    cases hbv : b i
    · rfl
    · exact absurd (hcov i hi (by simp [hbv])) hiS
  apply Bool.eq_false_iff.mpr
  intro hall
  have hall' := (evalCNF_true_iff b _).mp hall
  by_cases hsome : ∃ j, j < k + 1 ∧ b j = true
  · obtain ⟨j, hj, hbj⟩ := hsome
    have hc := hall' [⟨j, false⟩, ⟨i, true⟩]
      (List.mem_cons_of_mem _ ((mem_trap_pairs k _).mpr ⟨j, i, hj, hi, rfl⟩))
    simp [evalClause, evalLit, hbj, hbi] at hc
  · have hc := hall' _ (List.mem_cons_self ..)
    obtain ⟨l, hl, hev⟩ := (evalClause_true_iff _ _).mp hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    exact hsome ⟨j, List.mem_range.mp hj, by simpa [evalLit] using hev⟩

/-- No fixed flip radius gives an exact neighbourhood for SAT: for every `k`,
`trapCNF k` is satisfiable, all-false has cost `1`, and every assignment
within `k` flips of all-false (on the formula's variables) costs at least `1`. -/
theorem bounded_flip_not_exact (k : Nat) :
    Satisfiable (trapCNF k) ∧ unsatCount (fun _ => false) (trapCNF k) = 1 ∧
      ∀ b, Within k (k + 1) (fun _ => false) b →
        unsatCount (fun _ => false) (trapCNF k) ≤ unsatCount b (trapCNF k) := by
  refine ⟨⟨_, trapCNF_allTrue k⟩, trapCNF_allFalse_cost k, fun b hb => ?_⟩
  rw [trapCNF_allFalse_cost]
  have h := trapCNF_near_allFalse k b hb
  apply Nat.pos_of_ne_zero
  intro h0
  rw [(unsatCount_eq_zero_iff b _).mp h0] at h
  cases h

end Issue532.Idea06
