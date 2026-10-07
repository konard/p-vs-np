import proofs.experiments.issue624.lean.RunCNF

/-! Initial row wiring. Symbolic cells read two certificate variables each;
no certificate, configuration, or trace enumeration is used. -/
namespace Issue624.InitialCNF
open Complexity Issue532.Machines Issue568.Tableau Issue624.LocalCNF
open Issue624.MachineCNF Issue624.SuccessorCNF Issue624.CertificateCNF
open Issue624.VerifierTableau Issue624.FixedWindow

inductive Source where
  | fixed (symbol : Symbol)
  | certificate (position : Nat)
  deriving Repr

def Source.eval (a : Assignment) : Source → Symbol
  | .fixed s => s
  | .certificate i => if a (2 * i) then Symbol.ofBool (a (2 * i + 1)) else .blank

def sourceCNF (base : Nat) : Source → CNF
  | .fixed s => [[⟨base + s.index, true⟩]]
  | .certificate i =>
    [implies [⟨2 * i, false⟩] [⟨base, true⟩],
     implies [⟨2 * i, true⟩, ⟨2 * i + 1, false⟩] [⟨base + 1, true⟩],
     implies [⟨2 * i, true⟩, ⟨2 * i + 1, true⟩] [⟨base + 2, true⟩]]

theorem sourceCNF_models (a : Assignment) (base : Nat) (s : Source) :
    evalCNF a (sourceCNF base s) = true ↔ a (base + (s.eval a).index) = true := by
  cases s with
  | fixed s => simp [sourceCNF, Source.eval, evalCNF, evalClause, evalLit]
  | certificate i =>
    cases hp : a (2 * i) <;> cases hb : a (2 * i + 1) <;>
      simp [sourceCNF, Source.eval, implies, negate, evalCNF, evalClause, evalLit,
        hp, hb, Symbol.ofBool, Symbol.index]

def tapeCNF (base : Nat) : List Source → CNF
  | [] => []
  | s :: rest => sourceCNF base s ++ tapeCNF (base + 4) rest

def TapeSelected (a : Assignment) (base : Nat) : List Symbol → Prop
  | [] => True
  | s :: rest => a (base + s.index) = true ∧ TapeSelected a (base + 4) rest

theorem tapeCNF_models (a : Assignment) (base : Nat) (sources : List Source) :
    evalCNF a (tapeCNF base sources) = true ↔
      TapeSelected a base (sources.map (Source.eval a)) := by
  induction sources generalizing base with
  | nil => simp [tapeCNF, evalCNF, TapeSelected]
  | cons s rest ih => simp [tapeCNF, sourceCNF_models, ih, TapeSelected]

theorem tapeSelected_iff (a : Assignment) (base : Nat) (xs : List Symbol) :
    TapeSelected a base xs ↔ ∀ i, (hi : i < xs.length) → a (base + 4 * i + (xs[i]'hi).index) = true := by
  induction xs generalizing base with
  | nil => simp [TapeSelected]
  | cons s xs ih =>
    simp only [TapeSelected, ih]
    constructor
    · rintro ⟨hs, ht⟩ i hi
      cases i with
      | zero => simpa using hs
      | succ i => simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, List.getElem_cons] using ht i (by simpa using hi)
    · intro h
      constructor
      · exact h 0 (by simp)
      · intro i hi
        have hh := h (i + 1) (by simpa using hi)
        change a (base + 4 * (i + 1) + (xs[i]).index) = true at hh
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

/-- All certificate slots, with actual bits followed by blanks. -/
def certificateSources (start : Nat) : Nat → List Source
  | 0 => []
  | n + 1 => .certificate start :: certificateSources (start + 1) n

@[simp] theorem certificateSources_length (start bound : Nat) :
    (certificateSources start bound).length = bound := by
  induction bound generalizing start <;> simp [certificateSources, *]

theorem certificateSources_eval (a : Assignment) (start bound : Nat) (cert : Word)
    (hr : Represents a start cert bound) :
    (certificateSources start bound).map (Source.eval a) =
      cert.map Symbol.ofBool ++ blanks (bound - cert.length) := by
  induction bound generalizing start cert with
  | zero => cases cert <;> simp_all [Represents, certificateSources, blanks]
  | succ n ih =>
    cases cert with
    | nil =>
      simp only [Represents] at hr
      rw [certificateSources, List.map_cons, Source.eval, hr.1]
      simp [ih _ [] hr.2.2, blanks, List.replicate_succ]
    | cons b cert =>
      have hb := represents_length hr.2.2
      rw [certificateSources, List.map_cons, Source.eval, hr.1]
      simp [hr.2.1, ih _ cert hr.2.2, List.length_cons, Nat.succ_sub_succ_eq_sub]

def inputSources (v : VerifierProgram) (x : Word) (bound : Nat) : List Source :=
  let bits := x.map (fun b => Source.fixed (Symbol.ofBool b))
  match v with
  | .ignoreCertificate _ => bits
  | .paired _ => bits ++ [.fixed .separator] ++ certificateSources 0 bound

def windowSources (v : VerifierProgram) (x : Word) (bound margin width : Nat) : List Source :=
  List.replicate margin (.fixed .blank) ++ inputSources v x bound ++
    List.replicate (width - margin - (inputSources v x bound).length) (.fixed .blank)

theorem windowSources_length (v : VerifierProgram) (x : Word) (bound margin width : Nat)
    (h : margin + (inputSources v x bound).length ≤ width) :
    (windowSources v x bound margin width).length = width := by
  simp only [windowSources, List.length_append, List.length_replicate]
  omega

private theorem flatten_fit_initial (xs : List Symbol) (margin width : Nat)
    (hw : xs.length + margin < width) :
    flatten (fitWindow (initialSymbols xs) margin width) =
      blanks margin ++ xs ++ blanks (width - margin - xs.length) := by
  cases xs with
  | nil =>
    simp only [initialSymbols, fitWindow, flatten, span, List.nil_append,
      List.reverse_replicate, blanks, List.append_nil, List.length_nil]
    have he : width - margin = (width - 1 - margin) + 1 := by omega
    simp only [Nat.zero_add, Nat.sub_zero, he, List.replicate_succ]
  | cons s xs =>
    simp only [initialSymbols, fitWindow, flatten, span, List.nil_append,
      List.reverse_replicate, blanks, List.length_cons, List.length_nil]
    have he : width - (0 + 1 + xs.length) - margin = width - margin - (xs.length + 1) := by omega
    simp only [he, List.cons_append, List.append_assoc]

theorem windowSources_eval (np : ClassNP) (x : Word) (a : Assignment)
    (hf : evalCNF a (certificateCNF 0 (np.certBound.eval x.length)) = true) :
    (windowSources np.verifier x (np.certBound.eval x.length)
      (maxClock np x.length) (windowWidth np x.length)).map (Source.eval a) =
    flatten (fitWindow (verifierInitial np.verifier x
      (decodeCertificate a 0 (np.certBound.eval x.length)))
      (maxClock np x.length) (windowWidth np x.length)) := by
  let B := np.certBound.eval x.length
  let T := maxClock np x.length
  let W := windowWidth np x.length
  let cert := decodeCertificate a 0 B
  have hc : cert.length ≤ B := decodeCertificate_length _ _ _
  have hs := certificateSources_eval a 0 B cert ((certificateCNF_models _ _ _).mp hf)
  have hbl (k : Nat) : (List.replicate k (Source.fixed Symbol.blank)).map (Source.eval a) = blanks k := by
    simp [Source.eval, blanks]
  change (windowSources np.verifier x B T W).map (Source.eval a) = _
  cases hv : np.verifier with
  | ignoreCertificate m =>
    have hw : x.length + T < W := by dsimp [W, T, B, windowWidth]; omega
    rw [verifierInitial, initial, flatten_fit_initial _ T W (by simpa using hw)]
    simp [windowSources, inputSources, hbl, Source.eval]
  | paired m =>
    have hw : (x.map Symbol.ofBool ++ [Symbol.separator] ++ cert.map Symbol.ofBool).length + T < W := by
      simp only [List.length_append, List.length_map, List.length_singleton]
      dsimp [W, windowWidth]; omega
    rw [verifierInitial, pairedInput, flatten_fit_initial _ T W hw]
    simp only [windowSources, inputSources, List.map_append, List.map_map,
      List.map_cons, List.map_nil, Source.eval, hbl]
    rw [hs]
    simp only [List.length_append, List.length_map, List.length_singleton]
    have he : blanks (B - cert.length) ++ blanks (W - T - (x.length + 1 + B)) =
        blanks (W - T - (x.length + 1 + cert.length)) := by
      unfold blanks; rw [List.replicate_append_replicate]; congr 1; dsimp [W, windowWidth]; omega
    simp only [Function.comp_def, Source.eval, certificateSources_length, List.append_assoc, he]


/-- One-hot row plus fixed state/head and symbolic tape cells. -/
def initialCNF (base states margin : Nat) (sources : List Source) : CNF :=
  rowCNF base states sources.length ++
    [[⟨base, true⟩], [⟨base + states + margin, true⟩]] ++
    tapeCNF (base + states + sources.length) sources

theorem initialCNF_models (a : Assignment) (base states margin : Nat) (sources : List Source)
    (c : Config) (hw : span c = sources.length) (hq : c.state = 0)
    (hh : c.left.length = margin) (ht : flatten c = sources.map (Source.eval a)) :
    evalCNF a (initialCNF base states margin sources) = true ↔
      RowRepresents a base states sources.length c := by
  simp only [initialCNF, evalCNF_append, Bool.and_eq_true, evalCNF, evalClause,
    evalLit, Bool.and_true, Bool.or_false, beq_iff_eq, tapeCNF_models]
  constructor
  · rintro ⟨⟨hr, hq', hh'⟩, ht'⟩
    have hd := (rowCNF_models a base states sources.length).mp hr
    have hstate : (decodeRow a base states sources.length).state = c.state := by
      rw [hq]; exact (hd.2.1.2.2 0 (by have := hd.2.1.1; omega) (by simpa using hq')).symm
    have hhead : (decodeRow a base states sources.length).left.length = c.left.length := by
      rw [hh]; exact (hd.2.2.1.2.2 margin (by
        have : c.left.length < sources.length := by unfold span at hw; omega
        omega) hh').symm
    have hflat : flatten (decodeRow a base states sources.length) = flatten c := by
      apply List.ext_getElem
      · simp [hd.1, hw]
      · intro i hi hi'
        have hsel := hd.2.2.2 i (by simpa [flatten_length, hd.1] using hi)
        have hp := (tapeSelected_iff a _ _).mp ht' i (by simpa [← ht, flatten_length, hw] using hi')
        have hs := hsel.2.2 ((flatten c)[i]).index (symbolIndex_lt _)
          (by simpa [tapeBase, ← ht] using hp)
        have hs' := congrArg symbolOfIndex hs
        simpa [cell, List.getElem?_eq_getElem hi, symbolOfIndex_index] using hs'.symm
    have he := flatten_injective _ c hstate hhead hflat
    simpa [he] using hd
  · intro hr
    refine ⟨⟨rowRepresents_models _ _ _ _ _ hr, ?_, ?_⟩, ?_⟩
    · simpa [hq] using hr.2.1.2.1
    · simpa [hh] using hr.2.2.1.2.1
    · apply (tapeSelected_iff a _ _).mpr
      intro i hi
      have ht' := hr.2.2.2 i (by simpa using hi)
      simpa [tapeBase, cell, ht, List.getElem?_eq_getElem (by simpa [ht] using hi)] using ht'.2.1

def SourceBound (bound : Nat) : Source → Prop
  | .fixed _ => True
  | .certificate i => i < bound

theorem sourceCNF_length (base : Nat) (s : Source) : (sourceCNF base s).length ≤ 3 := by
  cases s <;> simp [sourceCNF]

theorem sourceCNF_bounds (base bound limit : Nat) (s : Source)
    (hb : base + 4 ≤ limit) (hc : 2 * bound ≤ limit) (hs : SourceBound bound s) :
    VarsBelow limit (sourceCNF base s) ∧ ∀ c ∈ sourceCNF base s, c.length ≤ 3 := by
  cases s with
  | fixed s =>
    have h := symbolIndex_lt s
    simp [sourceCNF, VarsBelow]; omega
  | certificate i =>
    simp only [SourceBound] at hs
    simp [sourceCNF, VarsBelow, implies, negate]
    omega

theorem tapeCNF_length (base : Nat) (sources : List Source) :
    (tapeCNF base sources).length ≤ 3 * sources.length := by
  induction sources generalizing base with
  | nil => simp [tapeCNF]
  | cons s sources ih =>
    have hs := sourceCNF_length base s
    have ht := ih (base + 4)
    simp only [tapeCNF, List.length_append, List.length_cons]
    omega

theorem tapeCNF_bounds (base bound limit : Nat) (sources : List Source)
    (hb : base + 4 * sources.length ≤ limit) (hc : 2 * bound ≤ limit)
    (hs : ∀ s ∈ sources, SourceBound bound s) :
    VarsBelow limit (tapeCNF base sources) ∧ ∀ c ∈ tapeCNF base sources, c.length ≤ 3 := by
  induction sources generalizing base with
  | nil => simp [tapeCNF, VarsBelow]
  | cons s rest ih =>
    have hh := sourceCNF_bounds base bound limit s (by simp only [List.length_cons] at hb; omega)
      hc (hs s (by simp))
    have ht := ih (base + 4) (by simp only [List.length_cons] at hb; omega)
      (fun s h => hs s (List.mem_cons_of_mem _ h))
    constructor
    · intro c h l hl
      rcases List.mem_append.mp h with h | h
      · exact hh.1 c h l hl
      · exact ht.1 c h l hl
    · intro c h
      rcases List.mem_append.mp h with h | h
      · exact hh.2 c h
      · exact ht.2 c h

theorem certificateSources_bound (start bound : Nat) :
    ∀ s ∈ certificateSources start bound, SourceBound (start + bound) s := by
  induction bound generalizing start with
  | zero => simp [certificateSources]
  | succ k ih =>
    intro s hs
    simp only [certificateSources, List.mem_cons] at hs
    rcases hs with rfl | hs
    · simp [SourceBound]
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (start + 1) s hs

theorem windowSources_bound (v : VerifierProgram) (x : Word) (bound margin width : Nat) :
    ∀ s ∈ windowSources v x bound margin width, SourceBound bound s := by
  intro s hs
  simp only [windowSources, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · have he := List.eq_of_mem_replicate hs; subst s; trivial
  · cases v with
    | ignoreCertificate m =>
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs; trivial
    | paired m =>
      simp only [inputSources, List.mem_append, List.mem_singleton] at hs
      rcases hs with (hs | rfl) | hs
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs; trivial
      · trivial
      · simpa using certificateSources_bound 0 bound s hs
  · have he := List.eq_of_mem_replicate hs; subst s; trivial

theorem initialCNF_length (base states margin : Nat) (sources : List Source) :
    (initialCNF base states margin sources).length ≤
      states * states + sources.length * sources.length + 20 * sources.length + 4 := by
  have hr := rowCNF_length base states sources.length
  have ht := tapeCNF_length (base + states + sources.length) sources
  simp only [initialCNF, List.length_append, List.length_cons, List.length_nil]
  omega

theorem initialCNF_bounds (base states margin bound : Nat) (sources : List Source)
    (hm : margin < sources.length) (hc : 2 * bound ≤ base)
    (hs : ∀ s ∈ sources, SourceBound bound s) :
    VarsBelow (base + states + 5 * sources.length) (initialCNF base states margin sources) ∧
    ∀ c ∈ initialCNF base states margin sources, c.length ≤ states + sources.length + 6 := by
  have hr := rowCNF_bounds base states sources.length
  have ht := tapeCNF_bounds (base + states + sources.length) bound
    (base + states + 5 * sources.length) sources (by omega) (by omega) hs
  constructor
  · intro c h l hl
    simp only [initialCNF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (h | rfl | rfl) | h
    · exact hr.1 c h l hl
    · simp only [List.mem_singleton] at hl; subst l; simp; omega
    · simp only [List.mem_singleton] at hl; subst l; simp; omega
    · exact ht.1 c h l hl
  · intro c h
    simp only [initialCNF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (h | rfl | rfl) | h
    · exact Nat.le_trans (hr.2 c h) (by omega)
    · simp
    · simp
    · exact Nat.le_trans (ht.2 c h) (by omega)

def initialPolynomial (states : Nat) (b w : Polynomial) : Polynomial :=
  let c := fun n => Polynomial.mk n 0
  let q := c states
  let count := polyAdd (polyAdd (polyAdd (polyMul q q) (polyMul w w))
    (polyMul (c 20) w)) (c 4)
  let width := polyAdd (polyAdd q w) (c 6)
  let variables := polyAdd (polyAdd (polyAdd b q) (polyMul (c 5) w)) (c 1)
  polyMul (polyMul (c 2) count) (polyAdd (c 1) (polyMul width variables))

theorem initialCNF_polynomial_size (states : Nat) (b w : Polynomial)
    (n base margin bound : Nat) (sources : List Source)
    (hb : base ≤ b.eval n) (hw : sources.length ≤ w.eval n)
    (hm : margin < sources.length) (hc : 2 * bound ≤ base)
    (hs : ∀ s ∈ sources, SourceBound bound s) :
    (encodeCNF (initialCNF base states margin sources)).length ≤
      (initialPolynomial states b w).eval n := by
  have add (p q : Polynomial) (u v : Nat) (hu : u ≤ p.eval n) (hv : v ≤ q.eval n) :
      u + v ≤ (polyAdd p q).eval n := Nat.le_trans (Nat.add_le_add hu hv) (polyAdd_eval p q n)
  have mul (p q : Polynomial) (u v : Nat) (hu : u ≤ p.eval n) (hv : v ≤ q.eval n) :
      u * v ≤ (polyMul p q).eval n := by rw [← polyMul_eval]; exact Nat.mul_le_mul hu hv
  have const (k : Nat) : k ≤ (Polynomial.mk k 0).eval n := by simp [Polynomial.eval]
  have hcount := add _ _ _ _ (add _ _ _ _ (add _ _ _ _
    (mul _ _ _ _ (const states) (const states)) (mul _ _ _ _ hw hw))
    (mul _ _ _ _ (const 20) hw)) (const 4)
  have hwidth := add _ _ _ _ (add _ _ _ _ (const states) hw) (const 6)
  have hvars := add _ _ _ _ (add _ _ _ _ (add _ _ _ _ hb (const states))
    (mul _ _ _ _ (const 5) hw)) (const 1)
  have hsize := mul _ _ _ _ (mul _ _ _ _ (const 2) hcount)
    (add _ _ _ _ (const 1) (mul _ _ _ _ hwidth hvars))
  have hf := initialCNF_bounds base states margin bound sources hm hc hs
  have henc := cnf_encoded_size _ _ _ hf.1 hf.2
  have hlen := initialCNF_length base states margin sources
  have henc' := Nat.le_trans henc (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hlen))
  exact Nat.le_trans henc' hsize

end Issue624.InitialCNF
