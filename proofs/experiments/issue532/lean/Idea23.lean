import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 23: resolution and the Cook–Reckhow framework

Proved here, for every CNF:

* `derives_sound`: every clause derivable by resolution (with weakening)
  from `φ` is true under every assignment satisfying `φ`; hence
  `empty_derivable_unsat`;
* `lift`: a derivation from the restriction `restrict v b φ` lifts to a
  derivation from `φ` of the same clause extended by the literal `v = !b`;
* `resolution_complete`: every unsatisfiable CNF whose variables lie in
  `vs` derives the empty clause; together, `unsat_iff_derives_empty`;
* Cook–Reckhow, abstract part: for an abstract proof system for UNSAT
  (sound and complete verifier on proof strings), polynomial boundedness
  gives a short certificate characterisation of UNSAT
  (`bounded_certificate`); an exact decider gives a trivially bounded system
  (`fromDecider_bounded`), so the schema `NoPolyBoundedProofSystemFor` is
  false without an efficiency requirement (`unrestricted_obligation_false`);
* Cook–Reckhow, machine part: a proof system is a `Complexity.VerifierProgram`
  with a polynomial clock (`MachineProofSystem`); a polynomially bounded one
  puts its language in NP (`inNP_of_polyBounded`); every language in P has
  one (`proofSystem_of_inP`); some language has none
  (`exists_noPolyBounded`).

**Verdict.** Resolution is sound and complete, but refuted in full strength
as a polynomial method: Haken (1985) proved exponential lower bounds on
resolution refutations of the pigeonhole formulas (cited, not formalized).
Cook's program is developed to the open obligation
`NoPolyBoundedUNSATProofSystem` (no polynomially bounded machine proof system
for `complement SAT`), which gives `¬ InP SAT` outright, P ≠ NP given
SAT ∈ NP, and is equivalent to NP ≠ coNP given the named known theorems
`CookReckhowNP`, `NPClosedUnderReductions` and the Cook–Levin halves
(`noPolyBounded_iff_npNeCoNP`).
Core Lean only.
-/

namespace Issue532.Idea23

/-! ## SAT core -/

structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool := if l.pos then a l.var else !(a l.var)

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: C => evalLit a l || evalClause a C

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | C :: φ => evalClause a C && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a, evalCNF a φ = true

theorem evalClause_true_iff (a : Assignment) (C : Clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLit a l = true := by
  induction C with
  | nil => simp [evalClause]
  | cons l C ih => simp [evalClause, ih]

theorem evalCNF_true_iff (a : Assignment) (φ : CNF) :
    evalCNF a φ = true ↔ ∀ C ∈ φ, evalClause a C = true := by
  induction φ with
  | nil => simp [evalCNF]
  | cons C φ ih => simp [evalCNF, ih]

/-! ## Restriction -/

/-- `clauseHas v b C`: `C` contains the literal "`v` has value `b`". -/
def clauseHas (v : Nat) (b : Bool) : Clause → Bool
  | [] => false
  | l :: C => (l.var == v && l.pos == b) || clauseHas v b C

/-- Delete every literal on variable `v`. -/
def removeVar (v : Nat) : Clause → Clause
  | [] => []
  | l :: C => if l.var = v then removeVar v C else l :: removeVar v C

/-- Set `v := b`: drop satisfied clauses, shorten the others. -/
def restrict (v : Nat) (b : Bool) : CNF → CNF
  | [] => []
  | C :: φ => if clauseHas v b C then restrict v b φ else removeVar v C :: restrict v b φ

/-- Update an assignment at one variable. -/
def setVar (a : Assignment) (v : Nat) (b : Bool) : Assignment :=
  fun x => if x = v then b else a x

theorem evalClause_setVar (a : Assignment) (v : Nat) (b : Bool) (C : Clause) :
    evalClause (setVar a v b) C = (clauseHas v b C || evalClause a (removeVar v C)) := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    by_cases h : l.var = v
    · have e : evalLit (setVar a v b) l = (l.pos == b) := by
        cases hp : l.pos <;> cases b <;> simp [evalLit, setVar, h, hp]
      simp only [evalClause, clauseHas, removeVar, h, ↓reduceIte, e, ih]
      cases (l.pos == b) <;> cases clauseHas v b C <;> simp
    · have e : evalLit (setVar a v b) l = evalLit a l := by
        simp [evalLit, setVar, h]
      simp only [evalClause, clauseHas, removeVar, h, ↓reduceIte, e, ih]
      have hv : (l.var == v) = false := by simp [h]
      rw [hv, Bool.false_and, Bool.false_or]
      cases evalLit a l <;> cases clauseHas v b C <;> simp

/-- **Restriction lemma.** -/
theorem eval_restrict (a : Assignment) (v : Nat) (b : Bool) (φ : CNF) :
    evalCNF a (restrict v b φ) = evalCNF (setVar a v b) φ := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    rw [evalCNF, evalClause_setVar]
    cases h : clauseHas v b C
    · simp [restrict, h, evalCNF, ih]
    · simp [restrict, h, ih]

theorem setVar_self (a : Assignment) (v : Nat) : setVar a v (a v) = a := by
  funext x
  by_cases h : x = v
  · subst h; simp [setVar]
  · simp [setVar, h]

/-- **Splitting rule.** -/
theorem sat_split (φ : CNF) (v : Nat) :
    Satisfiable φ ↔ Satisfiable (restrict v true φ) ∨ Satisfiable (restrict v false φ) := by
  constructor
  · rintro ⟨a, ha⟩
    have hr : evalCNF a (restrict v (a v) φ) = true := by
      rw [eval_restrict, setVar_self]; exact ha
    cases hv : a v
    · rw [hv] at hr; exact Or.inr ⟨a, hr⟩
    · rw [hv] at hr; exact Or.inl ⟨a, hr⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨setVar a v true, by rw [← eval_restrict]; exact ha⟩
    · exact ⟨setVar a v false, by rw [← eval_restrict]; exact ha⟩

/-! ## Variables -/

/-- All variables of `φ` occur in `vs`. -/
def VarsIn (φ : CNF) (vs : List Nat) : Prop := ∀ C ∈ φ, ∀ l ∈ C, l.var ∈ vs

theorem mem_removeVar (v : Nat) (C : Clause) (l : Lit) :
    l ∈ removeVar v C → l ∈ C ∧ l.var ≠ v := by
  induction C with
  | nil => simp [removeVar]
  | cons l' C ih =>
    by_cases h : l'.var = v
    · simp only [removeVar, h, ↓reduceIte]
      intro hl
      have := ih hl
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · simp only [removeVar, h, ↓reduceIte, List.mem_cons]
      rintro (rfl | hl)
      · exact ⟨Or.inl rfl, h⟩
      · have := ih hl
        exact ⟨Or.inr this.1, this.2⟩

theorem mem_restrict (v : Nat) (b : Bool) (φ : CNF) (C' : Clause) :
    C' ∈ restrict v b φ → ∃ C ∈ φ, C' = removeVar v C := by
  induction φ with
  | nil => simp [restrict]
  | cons C φ ih =>
    cases h : clauseHas v b C
    · simp only [restrict, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rintro (e | hm)
      · exact ⟨C, Or.inl rfl, e⟩
      · obtain ⟨D, hD, e⟩ := ih hm
        exact ⟨D, Or.inr hD, e⟩
    · simp only [restrict, h, ↓reduceIte]
      intro hm
      obtain ⟨D, hD, e⟩ := ih hm
      exact ⟨D, List.mem_cons_of_mem _ hD, e⟩

theorem restrict_vars (φ : CNF) (v : Nat) (vs : List Nat) (b : Bool)
    (h : VarsIn φ (v :: vs)) : VarsIn (restrict v b φ) vs := by
  intro C' hC' l hl
  obtain ⟨C, hC, e⟩ := mem_restrict v b φ C' hC'
  rw [e] at hl
  obtain ⟨hlC, hne⟩ := mem_removeVar v C l hl
  have := h C hC l hlC
  rcases List.mem_cons.mp this with e | e
  · exact absurd e hne
  · exact e

theorem eval_congr (a a' : Assignment) (φ : CNF)
    (h : ∀ C ∈ φ, ∀ l ∈ C, a l.var = a' l.var) : evalCNF a φ = evalCNF a' φ := by
  have hc : ∀ C ∈ φ, evalClause a C = evalClause a' C := by
    intro C hC
    have hC' := h C hC
    clear hC
    induction C with
    | nil => rfl
    | cons l C ih =>
      have hl : evalLit a l = evalLit a' l := by
        simp [evalLit, hC' l (List.mem_cons_self ..)]
      simp only [evalClause, hl, ih (fun l' hl' => hC' l' (List.mem_cons_of_mem _ hl'))]
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    simp only [evalCNF, hc C (List.mem_cons_self ..),
      ih (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))
        (fun C' hC' => hc C' (List.mem_cons_of_mem _ hC'))]

theorem sat_no_vars (φ : CNF) (h : VarsIn φ []) :
    Satisfiable φ ↔ evalCNF (fun _ => false) φ = true := by
  constructor
  · rintro ⟨a, ha⟩
    rw [eval_congr (fun _ => false) a φ (fun C hC l hl => absurd (h C hC l hl) (by simp))]
    exact ha
  · intro h'; exact ⟨_, h'⟩


/-! ## Size and the variables of a formula -/

/-- Input size: number of literal occurrences plus number of clauses. -/
def size : CNF → Nat
  | [] => 0
  | C :: φ => C.length + 1 + size φ

theorem length_removeVar_le (v : Nat) (C : Clause) : (removeVar v C).length ≤ C.length := by
  induction C with
  | nil => simp [removeVar]
  | cons l C ih =>
    by_cases h : l.var = v
    · simp only [removeVar, h, ↓reduceIte, List.length_cons]; omega
    · simp only [removeVar, h, ↓reduceIte, List.length_cons]; omega

/-- Restriction never increases the size. -/
theorem size_restrict_le (v : Nat) (b : Bool) (φ : CNF) : size (restrict v b φ) ≤ size φ := by
  induction φ with
  | nil => simp [restrict, size]
  | cons C φ ih =>
    have := length_removeVar_le v C
    cases h : clauseHas v b C
    · simp only [restrict, h, Bool.false_eq_true, ↓reduceIte, size]; omega
    · simp only [restrict, h, ↓reduceIte, size]; omega

/-- The list of variable occurrences of `φ` (with repetitions). -/
def varsOf : CNF → List Nat
  | [] => []
  | C :: φ => C.map Lit.var ++ varsOf φ

theorem varsOf_spec (φ : CNF) : VarsIn φ (varsOf φ) := by
  induction φ with
  | nil => intro C hC; simp at hC
  | cons D φ ih =>
    intro C hC l hl
    simp only [varsOf, List.mem_append]
    rcases List.mem_cons.mp hC with e | e
    · rw [e] at hl; exact Or.inl (List.mem_map.mpr ⟨l, hl, rfl⟩)
    · exact Or.inr (ih C e l hl)

theorem varsOf_length_le (φ : CNF) : (varsOf φ).length ≤ size φ := by
  induction φ with
  | nil => simp [varsOf, size]
  | cons C φ ih => simp only [varsOf, size, List.length_append, List.length_map]; omega


/-- `dec` decides satisfiability exactly, on every CNF. -/
def Decides (dec : CNF → Bool) : Prop := ∀ ψ, dec ψ = true ↔ Satisfiable ψ

/-- Polynomials in the repository form `c * (n+1)^k`. -/
def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

/-! ## An unconditional (exponential) decider -/

def solve : List Nat → CNF → Bool
  | [], φ => evalCNF (fun _ => false) φ
  | v :: vs, φ => solve vs (restrict v true φ) || solve vs (restrict v false φ)

theorem solve_correct (vs : List Nat) (φ : CNF) (h : VarsIn φ vs) :
    solve vs φ = true ↔ Satisfiable φ := by
  induction vs generalizing φ with
  | nil => exact (sat_no_vars φ h).symm
  | cons v vs ih =>
    rw [sat_split φ v, ← ih _ (restrict_vars φ v vs true h),
      ← ih _ (restrict_vars φ v vs false h)]
    simp [solve]

/-- The splitting decider of Idea 21, run on the variables of the input. -/
def satDec (φ : CNF) : Bool := solve (varsOf φ) φ

/-- An exact decider exists unconditionally; only its cost is in question. -/
theorem satDec_correct : Decides satDec := fun φ => solve_correct (varsOf φ) φ (varsOf_spec φ)

/-! ## Resolution -/

/-- Resolution derivations from `φ`: axioms, the resolution rule on a
variable `v`, and weakening to any clause containing all the literals. -/
inductive Derives (φ : CNF) : Clause → Prop
  | ax (C : Clause) : C ∈ φ → Derives φ C
  | res (v : Nat) (C₁ C₂ : Clause) :
      Derives φ (⟨v, true⟩ :: C₁) → Derives φ (⟨v, false⟩ :: C₂) → Derives φ (C₁ ++ C₂)
  | weak {C D : Clause} : Derives φ C → (∀ l ∈ C, l ∈ D) → Derives φ D

/-- **Soundness of resolution.** -/
theorem derives_sound {φ : CNF} {C : Clause} (h : Derives φ C) (a : Assignment)
    (ha : evalCNF a φ = true) : evalClause a C = true := by
  induction h with
  | ax C hC => exact (evalCNF_true_iff a φ).mp ha C hC
  | res v C₁ C₂ _ _ ih₁ ih₂ =>
    rw [evalClause_true_iff] at ih₁ ih₂ ⊢
    obtain ⟨l₁, hl₁, e₁⟩ := ih₁
    obtain ⟨l₂, hl₂, e₂⟩ := ih₂
    rcases List.mem_cons.mp hl₁ with r₁ | r₁
    · rcases List.mem_cons.mp hl₂ with r₂ | r₂
      · rw [r₁] at e₁
        rw [r₂] at e₂
        simp [evalLit] at e₁ e₂
        rw [e₁] at e₂
        exact absurd e₂ Bool.true_eq_false.mp
      · exact ⟨l₂, List.mem_append_right _ r₂, e₂⟩
    · exact ⟨l₁, List.mem_append_left _ r₁, e₁⟩
  | weak _ hsub ih =>
    rw [evalClause_true_iff] at ih ⊢
    obtain ⟨l, hl, e⟩ := ih
    exact ⟨l, hsub l hl, e⟩

/-- Deriving the empty clause certifies unsatisfiability. -/
theorem empty_derivable_unsat (φ : CNF) (h : Derives φ []) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  exact Bool.false_ne_true (derives_sound h a ha)

theorem mem_restrict_full (v : Nat) (b : Bool) (φ : CNF) (C' : Clause) :
    C' ∈ restrict v b φ → ∃ C ∈ φ, clauseHas v b C = false ∧ C' = removeVar v C := by
  induction φ with
  | nil => simp [restrict]
  | cons C φ ih =>
    cases h : clauseHas v b C
    · simp only [restrict, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rintro (e | hm)
      · exact ⟨C, Or.inl rfl, h, e⟩
      · obtain ⟨D, hD, hf, e⟩ := ih hm
        exact ⟨D, Or.inr hD, hf, e⟩
    · simp only [restrict, h, ↓reduceIte]
      intro hm
      obtain ⟨D, hD, hf, e⟩ := ih hm
      exact ⟨D, List.mem_cons_of_mem _ hD, hf, e⟩

theorem clauseHas_false (v : Nat) (b : Bool) (C : Clause) (h : clauseHas v b C = false)
    (l : Lit) (hl : l ∈ C) (hv : l.var = v) : l.pos = !b := by
  induction C with
  | nil => simp at hl
  | cons l' C ih =>
    simp only [clauseHas, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp hl with e | e
    · rw [← e] at h
      have h1 := h.1
      rw [hv] at h1
      cases hp : l.pos <;> cases b <;> simp_all
    · exact ih h.2 e

theorem mem_removeVar_of (v : Nat) (C : Clause) (l : Lit) (hl : l ∈ C) (hv : l.var ≠ v) :
    l ∈ removeVar v C := by
  induction C with
  | nil => simp at hl
  | cons l' C ih =>
    by_cases h : l'.var = v
    · simp only [removeVar, h, ↓reduceIte]
      rcases List.mem_cons.mp hl with e | e
      · rw [e] at hv; exact absurd h hv
      · exact ih e
    · simp only [removeVar, h, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.mp hl with e | e
      · exact Or.inl e
      · exact Or.inr (ih e)

/-- **Lifting lemma.**  A derivation of `D` from `restrict v b φ` gives a
derivation of `(v = !b) ∨ D` from `φ`. -/
theorem lift (v : Nat) (b : Bool) (φ : CNF) {D : Clause} (h : Derives (restrict v b φ) D) :
    Derives φ (⟨v, !b⟩ :: D) := by
  induction h with
  | ax D hD =>
    obtain ⟨C, hC, hf, e⟩ := mem_restrict_full v b φ D hD
    rw [e]
    apply Derives.weak (Derives.ax C hC)
    intro l hl
    by_cases hv : l.var = v
    · have hp := clauseHas_false v b C hf l hl hv
      have el : l = ⟨v, !b⟩ := by
        cases l with
        | mk lv lp => simp only at hv hp; rw [hv, hp]
      exact List.mem_cons.mpr (Or.inl el)
    · exact List.mem_cons_of_mem _ (mem_removeVar_of v C l hl hv)
  | res w C₁ C₂ _ _ ih₁ ih₂ =>
    have d₁ : Derives φ (⟨w, true⟩ :: (⟨v, !b⟩ :: C₁)) := by
      apply Derives.weak ih₁
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have d₂ : Derives φ (⟨w, false⟩ :: (⟨v, !b⟩ :: C₂)) := by
      apply Derives.weak ih₂
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    apply Derives.weak (Derives.res w _ _ d₁ d₂)
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with (h | h) | (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  | weak _ hsub ih =>
    apply Derives.weak ih
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons_of_mem _ (hsub x h)

/-- **Completeness of resolution.**  Every unsatisfiable CNF whose variables
lie in `vs` derives the empty clause. -/
theorem resolution_complete (vs : List Nat) :
    ∀ φ, VarsIn φ vs → ¬ Satisfiable φ → Derives φ [] := by
  induction vs with
  | nil =>
    intro φ hv hu
    cases φ with
    | nil => exact absurd ⟨fun _ => false, rfl⟩ hu
    | cons C φ =>
      cases C with
      | nil => exact Derives.ax [] (List.mem_cons_self ..)
      | cons l C =>
        have := hv (l :: C) (List.mem_cons_self ..) l (List.mem_cons_self ..)
        simp at this
  | cons v vs ih =>
    intro φ hv hu
    have h₁ : ¬ Satisfiable (restrict v true φ) := fun h => hu ((sat_split φ v).mpr (Or.inl h))
    have h₀ : ¬ Satisfiable (restrict v false φ) := fun h => hu ((sat_split φ v).mpr (Or.inr h))
    have d₁ : Derives φ [⟨v, false⟩] := lift v true φ (ih _ (restrict_vars φ v vs true hv) h₁)
    have d₀ : Derives φ [⟨v, true⟩] := lift v false φ (ih _ (restrict_vars φ v vs false hv) h₀)
    exact Derives.res v [] [] d₀ d₁

/-- Resolution characterises unsatisfiability exactly. -/
theorem unsat_iff_derives_empty (φ : CNF) : ¬ Satisfiable φ ↔ Derives φ [] :=
  ⟨resolution_complete (varsOf φ) φ (varsOf_spec φ), empty_derivable_unsat φ⟩

/-! ## Cook–Reckhow proof systems -/

/-- An abstract proof system for UNSAT: a verifier on proof strings that is
sound and complete.  (Cook–Reckhow additionally require the verifier to run
in polynomial time; that requirement is the parameter `Efficient` below.) -/
structure ProofSystem where
  verify : List Bool → CNF → Bool
  sound : ∀ π φ, verify π φ = true → ¬ Satisfiable φ
  complete : ∀ φ, ¬ Satisfiable φ → ∃ π, verify π φ = true

/-- Every unsatisfiable CNF has a proof of polynomial length. -/
def PolyBounded (P : ProofSystem) : Prop :=
  ∃ c k, ∀ φ, ¬ Satisfiable φ → ∃ π : List Bool, π.length ≤ polyEval c k (size φ) ∧ P.verify π φ = true

/-- **Bounded certificates.**  A polynomially bounded system turns UNSAT
into a guess-and-check statement with polynomially short certificates (an
NP-style characterisation of UNSAT when the verifier is efficient). -/
theorem bounded_certificate (P : ProofSystem) (h : PolyBounded P) :
    ∃ c k, ∀ φ, ¬ Satisfiable φ ↔
      ∃ π : List Bool, π.length ≤ polyEval c k (size φ) ∧ P.verify π φ = true := by
  obtain ⟨c, k, hb⟩ := h
  exact ⟨c, k, fun φ => ⟨hb φ, fun ⟨π, _, hv⟩ => P.sound π φ hv⟩⟩

/-- The proof system that ignores the proof and runs an exact decider. -/
def fromDecider (dec : CNF → Bool) (h : Decides dec) : ProofSystem where
  verify := fun _ φ => !dec φ
  sound := fun _ φ hv hs => by
    have hd := (h φ).mpr hs
    simp [hd] at hv
  complete := fun φ hu => ⟨[], by
    show (!dec φ) = true
    cases hd : dec φ with
    | false => rfl
    | true => exact absurd ((h φ).mp hd) hu⟩

theorem fromDecider_bounded (dec : CNF → Bool) (h : Decides dec) :
    PolyBounded (fromDecider dec h) :=
  ⟨0, 0, fun φ hu => by
    obtain ⟨π, hπ⟩ := (fromDecider dec h).complete φ hu
    exact ⟨[], Nat.zero_le _, hπ⟩⟩

/-- Generic schema over a free efficiency notion `Efficient`: no proof
system satisfying `Efficient` is polynomially bounded.  Its truth depends on
the choice of `Efficient` (`unrestricted_obligation_false`); the machine
version is `NoPolyBoundedUNSATProofSystem` below. -/
def NoPolyBoundedProofSystemFor (Efficient : ProofSystem → Prop) : Prop :=
  ∀ P, Efficient P → ¬ PolyBounded P

/-- Without an efficiency requirement the obligation is false: the
(exponential) splitting decider gives a system with empty proofs. -/
theorem unrestricted_obligation_false : ¬ NoPolyBoundedProofSystemFor (fun _ => True) :=
  fun h => h (fromDecider satDec satDec_correct) trivial (fromDecider_bounded satDec satDec_correct)

/-- **Conditional separation.**  If systems built from efficient exact
deciders are efficient, the obligation excludes efficient exact deciders
(for an honest efficiency notion: P ≠ NP). -/
theorem lower_bound_excludes_efficient_decider (Efficient : ProofSystem → Prop)
    (EffDec : (CNF → Bool) → Prop)
    (hclosed : ∀ dec (h : Decides dec), EffDec dec → Efficient (fromDecider dec h))
    (hlb : NoPolyBoundedProofSystemFor Efficient) :
    ∀ dec, Decides dec → ¬ EffDec dec :=
  fun dec h he => hlb _ (hclosed dec h he) (fromDecider_bounded dec h)

/-! # Machine part: Cook–Reckhow proof systems in the shared model

A proof system for a language `L` is a `Complexity.VerifierProgram` with an
explicit polynomial clock: on every input `x` and every proof string `π` it
halts within `timeBound` steps (in `|x| + |π|`), accepts only members of `L`,
and accepts every member with some proof.  The CNF formulas are those of the
shared layer (`Issue532.Machines.decode`), so UNSAT is `complement SAT`. -/

section MachinePart

open Complexity
open Issue532.Machines (SAT complement InCoNP NPEqualsCoNP SATInNP SATHard NPHard
  PolyReduces run_deterministic polyDec_iff_inP inP_complement complement_complement
  pNotEqualsNP_of_npNeCoNP inP_sat_of_pEqualsNP DecidesWithin
  exists_language_not_in_family encMachine encMachine_injective)

/-- A Cook–Reckhow proof system for `L` in the shared machine model: a
verifier machine that halts within the polynomial `timeBound` on every
(input, proof) pair, is sound for `L`, and is complete for `L`. -/
structure MachineProofSystem (L : Language) where
  verifier : VerifierProgram
  timeBound : Polynomial
  halts : ∀ x π, ∃ t b, t ≤ verifier.timeLimit timeBound x π ∧ verifier.Run x π t b
  sound : ∀ x π t, verifier.Run x π t true → L x = true
  complete : ∀ x, L x = true → ∃ π t, verifier.Run x π t true

/-- Polynomial boundedness: every member has an accepted proof of length
polynomial in the input length. -/
def MachineProofSystem.PolyBounded {L : Language} (P : MachineProofSystem L) : Prop :=
  ∃ q : Polynomial, ∀ x, L x = true → ∃ π t, π.length ≤ q.eval x.length ∧ P.verifier.Run x π t true

/-- Verifier runs are deterministic. -/
theorem verifierRun_deterministic {v : VerifierProgram} {x π : Word} {t t' : Nat} {b b' : Bool}
    (h : v.Run x π t b) (h' : v.Run x π t' b') : t = t' ∧ b = b' := by
  cases v with
  | ignoreCertificate m => exact run_deterministic h h'
  | paired m => exact run_deterministic h h'

/-- **A polynomially bounded machine proof system puts `L` in NP** (proved:
the proof bound is the certificate bound, and the clock plus determinism
bound the accepting run). -/
theorem inNP_of_polyBounded {L : Language} (P : MachineProofSystem L) (h : P.PolyBounded) :
    InNP L := by
  obtain ⟨q, hq⟩ := h
  refine ⟨{ language := L, verifier := P.verifier, timeBound := P.timeBound, certBound := q,
            terminates := fun x π _ => P.halts x π,
            correct := fun x => ⟨fun hx => ?_, fun ⟨π, t, _, _, hr⟩ => P.sound x π t hr⟩ }, rfl⟩
  obtain ⟨π, t, hlen, hr⟩ := hq x hx
  obtain ⟨t', b', ht', hr'⟩ := P.halts x π
  obtain ⟨rfl, _⟩ := verifierRun_deterministic hr hr'
  exact ⟨π, t, hlen, ht', hr⟩

/-- **Every language in P has a polynomially bounded proof system** (proved:
the decider ignores the proof; the empty proof suffices). -/
theorem proofSystem_of_inP {L : Language} (h : InP L) :
    ∃ P : MachineProofSystem L, P.PolyBounded := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  refine ⟨{ verifier := .ignoreCertificate m, timeBound := p,
            halts := fun x _ => ?_, sound := fun x _ t hr => ?_, complete := fun x hx => ?_ },
          ⟨⟨0, 0⟩, fun x hx => ?_⟩⟩
  · obtain ⟨t, b, ht, hr, _⟩ := hm x
    exact ⟨t, b, ht, hr⟩
  · obtain ⟨t', b', _, hr', hb'⟩ := hm x
    obtain ⟨_, rfl⟩ := run_deterministic hr hr'
    exact hb'.symm
  · obtain ⟨t, b, _, hr, hb⟩ := hm x
    rw [hx] at hb
    subst hb
    exact ⟨[], t, hr⟩
  · obtain ⟨t, b, _, hr, hb⟩ := hm x
    rw [hx] at hb
    subst hb
    exact ⟨[], t, Nat.zero_le _, hr⟩

/-- `L` has no polynomially bounded machine proof system. -/
def NoPolyBoundedMachineProofSystem (L : Language) : Prop :=
  ∀ P : MachineProofSystem L, ¬ P.PolyBounded

/-- **Open obligation (Cook's program).**  UNSAT (`complement SAT`, over the
CNF encoding of the shared layer) has no polynomially bounded proof system
whose verifier is a polynomial-time machine.  With the known theorems
`CookReckhowNP` and `NPClosedUnderReductions` and the Cook–Levin halves,
this is equivalent to NP ≠ coNP (`noPolyBounded_iff_npNeCoNP`). -/
def NoPolyBoundedUNSATProofSystem : Prop :=
  NoPolyBoundedMachineProofSystem (complement SAT)

/-- A language in P has a polynomially bounded system, so the property is
not vacuously true. -/
theorem not_noPolyBounded_of_inP {L : Language} (h : InP L) :
    ¬ NoPolyBoundedMachineProofSystem L := by
  obtain ⟨P, hP⟩ := proofSystem_of_inP h
  exact fun hno => hno P hP

/-- A language outside NP has no polynomially bounded system. -/
theorem noPolyBounded_of_not_inNP {L : Language} (h : ¬ InNP L) :
    NoPolyBoundedMachineProofSystem L :=
  fun P hP => h (inNP_of_polyBounded P hP)

/-- Injective encoding of verifier programs. -/
def encVerifier : VerifierProgram → Word
  | .ignoreCertificate m => false :: encMachine m
  | .paired m => true :: encMachine m

theorem encVerifier_injective (v w : VerifierProgram) (h : encVerifier v = encVerifier w) :
    v = w := by
  cases v <;> cases w <;> simp only [encVerifier, List.cons.injEq] at h
  · rw [encMachine_injective h.2]
  · cases h.1
  · cases h.1
  · rw [encMachine_injective h.2]

open Classical in
/-- The language whose members are the inputs with some accepted proof. -/
noncomputable def verifierLanguage (v : VerifierProgram) : Language :=
  fun x => decide (∃ π t, v.Run x π t true)

theorem verifierLanguage_eq {L : Language} (P : MachineProofSystem L) :
    verifierLanguage P.verifier = L := by
  classical
  funext x
  simp only [verifierLanguage]
  cases hx : L x with
  | true => exact decide_eq_true (P.complete x hx)
  | false =>
    refine decide_eq_false fun ⟨π, t, hr⟩ => ?_
    rw [P.sound x π t hr] at hx
    cases hx

/-- **Non-vacuity.**  Some language has no machine proof system at all, so
in particular no polynomially bounded one (Cantor over encoded verifiers). -/
theorem exists_noPolyBounded : ∃ L : Language, NoPolyBoundedMachineProofSystem L := by
  obtain ⟨L, hL⟩ := exists_language_not_in_family encVerifier encVerifier_injective verifierLanguage
  exact ⟨L, fun P _ => hL P.verifier (verifierLanguage_eq P)⟩

/-- **Conditional theorem (proved).**  The obligation gives `¬ InP SAT`
unconditionally: otherwise `complement SAT` is in P and has a system with
empty proofs. -/
theorem not_inP_sat_of_noPolyBounded (h : NoPolyBoundedUNSATProofSystem) : ¬ InP SAT :=
  fun hs => not_noPolyBounded_of_inP (inP_complement hs) h

/-- **Conditional theorem (proved).**  With SAT ∈ NP (one half of the
Cook–Levin theorem, a named hypothesis) the obligation gives P ≠ NP. -/
theorem pNotEqualsNP_of_noPolyBounded (mem : SATInNP) (h : NoPolyBoundedUNSATProofSystem) :
    PNotEqualsNP :=
  fun hp => not_inP_sat_of_noPolyBounded h (inP_sat_of_pEqualsNP mem hp)

/-- Known theorem, not mechanised here: every NP language has a polynomially
bounded machine proof system.  The verifier is the NP verifier run with a
clock that also rejects proofs longer than the certificate bound (Cook and
Reckhow, "The relative efficiency of propositional proof systems", J.
Symbolic Logic 44(1), 1979).  The converse direction is proved
(`inNP_of_polyBounded`). -/
def CookReckhowNP : Prop :=
  ∀ L : Language, InNP L → ∃ P : MachineProofSystem L, P.PolyBounded

/-- Known theorem, not mechanised here: NP is closed under polynomial-time
many-one reductions (Karp, "Reducibility among combinatorial problems",
1972; Arora and Barak, "Computational Complexity", 2009, Section 2.2). -/
def NPClosedUnderReductions : Prop :=
  ∀ L L' : Language, PolyReduces L L' → InNP L' → InNP L

/-- A reduction from `L` to `L'` is also one from the complements. -/
theorem polyReduces_complement {L L' : Language} (h : PolyReduces L L') :
    PolyReduces (complement L) (complement L') := by
  obtain ⟨m, f, p, hc, hf⟩ := h
  exact ⟨m, f, p, hc, fun x => by simp [complement, hf x]⟩

/-- **Conditional theorem (proved).**  The obligation gives NP ≠ coNP, given
SAT ∈ NP and `CookReckhowNP`; then P ≠ NP by `pNotEqualsNP_of_npNeCoNP`. -/
theorem npNeCoNP_of_noPolyBounded (mem : SATInNP) (hcr : CookReckhowNP)
    (h : NoPolyBoundedUNSATProofSystem) : ¬ NPEqualsCoNP := by
  intro heq
  obtain ⟨P, hP⟩ := hcr _ ((heq SAT).mp mem)
  exact h P hP

theorem pNotEqualsNP_via_coNP (mem : SATInNP) (hcr : CookReckhowNP)
    (h : NoPolyBoundedUNSATProofSystem) : PNotEqualsNP :=
  pNotEqualsNP_of_npNeCoNP (npNeCoNP_of_noPolyBounded mem hcr h)

/-- **Converse (proved from named hypotheses).**  A polynomially bounded
system for UNSAT gives NP = coNP, given SAT's NP-hardness and closure of NP
under reductions. -/
theorem npEqualsCoNP_of_polyBounded (hard : SATHard) (hclosed : NPClosedUnderReductions)
    (P : MachineProofSystem (complement SAT)) (hP : P.PolyBounded) : NPEqualsCoNP := by
  have hu : InNP (complement SAT) := inNP_of_polyBounded P hP
  intro L
  constructor
  · intro hL
    exact hclosed _ _ (polyReduces_complement (hard L hL)) hu
  · intro hL
    have hr := polyReduces_complement (hard _ hL)
    rw [complement_complement] at hr
    exact hclosed _ _ hr hu

/-- **Cook–Reckhow equivalence (proved from named hypotheses).** -/
theorem noPolyBounded_iff_npNeCoNP (mem : SATInNP) (hard : SATHard) (hcr : CookReckhowNP)
    (hclosed : NPClosedUnderReductions) :
    NoPolyBoundedUNSATProofSystem ↔ ¬ NPEqualsCoNP :=
  ⟨npNeCoNP_of_noPolyBounded mem hcr,
   fun hne P hP => hne (npEqualsCoNP_of_polyBounded hard hclosed P hP)⟩

end MachinePart

end Issue532.Idea23
