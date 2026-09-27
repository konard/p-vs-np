import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 16: diagonalization and relativization

Abstract part, proved for all enumerations, oracles and parameters:

* `diag_ne`, `no_enumeration_of_all`: Cantor/Turing diagonal. For every
  enumeration `e : ℕ → ℕ → Bool`, the language `diag e n = !(e n n)` differs
  from every `e i`.
* `hierarchy_abstract`, `hierarchy_strict`: the abstract time-hierarchy
  argument. If a class `C` is enumerated by `e` and a universal evaluator `u`
  satisfies `u i x = e i x`, the diagonal language is decidable with one query
  to `u` but is not in `C`.
* `diag_relativizes`, `hierarchy_relativizes`, `diagTech_relativizing`: both
  arguments go through verbatim for every oracle world `O : ℕ → Bool`.
* `no_relativizing_proof`, `relativizing_cannot_prove`,
  `diagonalization_cannot_prove`, `ingredient_necessary`: a statement that
  fails in some oracle world has no relativizing proof.
  `NonRelativizingIngredientFor` is the generic schema of what a proof would
  have to add.
* `oracle_adversary`, `testLang_one_certificate`: the query-complexity core of
  the BGS oracle `B`.

Machine part, in the shared model `Complexity.Machine` / `Issue532.Machines`:

* Oracle machines `OMachine` extend `Complexity.Machine` by a query instruction
  (`ostep`, `ORun`). `orun_lift_iff`: ordinary machines are oracle machines
  that never query. `run_lower_iff`: against a constant oracle an oracle machine
  is an ordinary machine.
* `InPO A`, `InNPO A`, `PEqualsNPO A` are `P^A`, `NP^A`, `P^A = NP^A`.
  `inPO_const_iff`, `inNPO_const_iff`, `pEqualsNPO_const_iff`: for a constant
  oracle they are exactly `InP`, `InNP`, `PEqualsNP`.
  `pEqualsNP_of_all_oracles`, `pNotEqualsNP_of_all_oracles`: a relativizing
  proof would settle the real question.
* `BGSCollapse`, `BGSSeparation`: the Baker–Gill–Solovay theorem as named
  known-theorem hypotheses. `bgs_no_uniform_answer`: under them, neither answer
  holds for every oracle.
* `diagonal_core`, `diagWithin_not_decidedWithin`: the diagonal half of the time
  hierarchy, proved for machines with polynomial clocks.
  `timeHierarchy_of_universalSimulation`: `TimeHierarchy` from the known
  `UniversalSimulation`. `diagWithinO_not_decidedWithin`,
  `timeHierarchyO_of_universalSimulationO`: the same relative to every oracle.
* `InDTIME`, `InNTIME`, `NTimeHierarchyGap`, `NTimeHierarchy`: time classes and
  the nondeterministic time hierarchy (known theorem, stated as a hypothesis),
  with the non-vacuity theorems `exists_not_inDTIME`, `exists_not_inNTIME`.

Verdict: pure diagonalization is refuted as a route to P vs NP, in full
strength, by the published BGS theorem (`bgs_no_uniform_answer`). The formal
core is the proof that the diagonal argument relativizes. Nothing here proves or
refutes P = NP.
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
Generic schema over a free technique `T` (not assumed, not a machine-level
statement): `T` is sound for the real world `real`, proves `S`, and does not
relativize. The machine-level content of the barrier is `bgs_no_uniform_answer`.
-/
def NonRelativizingIngredientFor (T : Technique) (real : World) (S : World → Prop) : Prop :=
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

/-! # Machine part: the barrier in the shared machine model -/

open Complexity Issue532.Machines

/-! ## Oracle machines: a real extension of `Complexity.Machine` -/

/-- An oracle is a language: the query `y` is answered by `A y`. -/
abbrev Oracle := Language

/-- An oracle-machine instruction: an ordinary `Complexity.Instruction`, or a
query that asks the oracle about the bit word starting at the head (up to the
first blank or separator) and moves to state `yes` or `no`. A query is one step. -/
inductive OInstruction where
  | base (i : Instruction)
  | query (yes no : Nat)

/-- An oracle machine: a finite instruction table, as for `Complexity.Machine`. -/
structure OMachine where
  program : List (List OInstruction)

/-- Table lookup; a missing instruction rejects, as in `Complexity.Machine`. -/
def oinstruction (m : OMachine) (q : Nat) (a : Symbol) : OInstruction :=
  ((m.program[q]?).bind fun row => row[a.index]?).getD (.base (.halt false))

/-- The query word: the bits from the head rightwards, up to the first blank or
separator. -/
def queryWord : List Symbol → Word
  | .zero :: r => false :: queryWord r
  | .one :: r => true :: queryWord r
  | _ => []

/-- One step of an oracle machine with oracle `A`. -/
def ostep (A : Oracle) (m : OMachine) (c : Config) : Bool ⊕ Config :=
  match oinstruction m c.state c.head with
  | .base (.halt b) => .inl b
  | .base (.move next write dir) => .inr (moveHead c next write dir)
  | .query yes no =>
    .inr ⟨if A (queryWord (c.head :: c.right)) then yes else no, c.left, c.head, c.right⟩

/-- Halting runs of an oracle machine, with the step count `t` (as `Complexity.Run`). -/
inductive ORun (A : Oracle) (m : OMachine) : Config → Nat → Bool → Prop where
  | halt {c b} : ostep A m c = .inl b → ORun A m c 1 b
  | next {c c' t b} : ostep A m c = .inr c' → ORun A m c' t b → ORun A m c (t + 1) b

theorem orun_deterministic {A : Oracle} {m : OMachine} {c : Config} {t t' : Nat} {b b' : Bool}
    (h : ORun A m c t b) (h' : ORun A m c t' b') : t = t' ∧ b = b' := by
  induction h generalizing t' with
  | halt hs =>
    cases h' with
    | halt hs' => rw [hs] at hs'; cases hs'; exact ⟨rfl, rfl⟩
    | next hs' _ => rw [hs] at hs'; cases hs'
  | next hs _ ih =>
    cases h' with
    | halt hs' => rw [hs] at hs'; cases hs'
    | next hs' hr' =>
      rw [hs] at hs'
      cases hs'
      obtain ⟨h1, h2⟩ := ih hr'
      exact ⟨by rw [h1], h2⟩

/-- Every ordinary machine is an oracle machine that never queries. -/
def liftMachine (m : Machine) : OMachine := ⟨m.program.map (List.map OInstruction.base)⟩

theorem lift_instruction (m : Machine) (q : Nat) (a : Symbol) :
    oinstruction (liftMachine m) q a = .base (Complexity.Machine.instruction m q a) := by
  unfold oinstruction liftMachine Complexity.Machine.instruction
  simp only [List.getElem?_map]
  cases m.program[q]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Option.bind_some, List.getElem?_map]
    cases row[a.index]? <;> rfl

theorem ostep_lift (A : Oracle) (m : Machine) (c : Config) :
    ostep A (liftMachine m) c = step m c := by
  unfold ostep step
  rw [lift_instruction]
  cases Complexity.Machine.instruction m c.state c.head <;> rfl

/-- Runs of a lifted machine are the runs of the machine, for every oracle. -/
theorem orun_lift_iff (A : Oracle) (m : Machine) (c : Config) (t : Nat) (b : Bool) :
    ORun A (liftMachine m) c t b ↔ Run m c t b := by
  constructor
  · intro h
    induction h with
    | halt hs => exact .halt (by rw [← ostep_lift A]; exact hs)
    | next hs _ ih => exact .next (by rw [← ostep_lift A]; exact hs) ih
  · intro h
    induction h with
    | halt hs => exact .halt (by rw [ostep_lift]; exact hs)
    | next hs _ ih => exact .next (by rw [ostep_lift]; exact hs) ih

/-- The symbol with a given column index. -/
def symbolOfIndex : Nat → Symbol
  | 0 => .blank
  | 1 => .zero
  | 2 => .one
  | _ => .separator

theorem symbolOfIndex_index (a : Symbol) : symbolOfIndex a.index = a := by
  cases a <;> rfl

/-- Against the constant oracle `fun _ => b`, a query is an ordinary move that
rewrites the scanned symbol and does not move. -/
def lowerInstruction (b : Bool) (a : Symbol) : OInstruction → Instruction
  | .base i => i
  | .query yes no => .move (if b then yes else no) a .stay

/-- The ordinary machine that simulates `m` against the constant oracle `fun _ => b`. -/
def lowerMachine (b : Bool) (m : OMachine) : Machine :=
  ⟨m.program.map fun row => row.mapIdx fun i oi => lowerInstruction b (symbolOfIndex i) oi⟩

theorem lower_instruction (b : Bool) (m : OMachine) (q : Nat) (a : Symbol) :
    Complexity.Machine.instruction (lowerMachine b m) q a =
      lowerInstruction b a (oinstruction m q a) := by
  unfold oinstruction lowerMachine Complexity.Machine.instruction
  simp only [List.getElem?_map]
  cases m.program[q]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Option.bind_some, List.getElem?_mapIdx]
    cases row[a.index]? with
    | none => rfl
    | some oi => simp [symbolOfIndex_index]

theorem step_lower (b : Bool) (m : OMachine) (c : Config) :
    step (lowerMachine b m) c = ostep (fun _ => b) m c := by
  unfold ostep step
  rw [lower_instruction]
  cases oinstruction m c.state c.head with
  | base i => cases i <;> rfl
  | query yes no => rfl

/-- Runs against a constant oracle are runs of an ordinary machine. -/
theorem run_lower_iff (b : Bool) (m : OMachine) (c : Config) (t : Nat) (r : Bool) :
    Run (lowerMachine b m) c t r ↔ ORun (fun _ => b) m c t r := by
  constructor
  · intro h
    induction h with
    | halt hs => exact .halt (by rw [← step_lower]; exact hs)
    | next hs _ ih => exact .next (by rw [← step_lower]; exact hs) ih
  · intro h
    induction h with
    | halt hs => exact .halt (by rw [step_lower]; exact hs)
    | next hs _ ih => exact .next (by rw [step_lower]; exact hs) ih

/-! ## Oracle classes `P^A`, `NP^A` -/

/-- `m` decides `L` with oracle `A` within the polynomial `p`. -/
def ODecidesWithin (A : Oracle) (m : OMachine) (p : Polynomial) (L : Language) : Prop :=
  ∀ x, ∃ t b, t ≤ p.eval x.length ∧ ORun A m (initial x) t b ∧ b = L x

/-- `L ∈ P^A`. -/
def InPO (A : Oracle) (L : Language) : Prop := ∃ (m : OMachine) (p : Polynomial), ODecidesWithin A m p L

/-- Oracle verifiers, mirroring `Complexity.VerifierProgram`. -/
inductive OVerifier where
  | ignoreCertificate (m : OMachine)
  | paired (m : OMachine)

def OVerifier.Run (v : OVerifier) (A : Oracle) (x cert : Word) (t : Nat) (b : Bool) : Prop :=
  match v with
  | .ignoreCertificate m => ORun A m (initial x) t b
  | .paired m => ORun A m (pairedInput x cert) t b

def OVerifier.timeLimit (v : OVerifier) (p : Polynomial) (x cert : Word) : Nat :=
  match v with
  | .ignoreCertificate _ => p.eval x.length
  | .paired _ => p.eval (x.length + cert.length + 1)

/-- `L ∈ NP^A`: the fields of `Complexity.ClassNP`, with an oracle verifier. -/
def InNPO (A : Oracle) (L : Language) : Prop :=
  ∃ (v : OVerifier) (timeBound certBound : Polynomial),
    (∀ x cert, cert.length ≤ certBound.eval x.length →
      ∃ t b, t ≤ v.timeLimit timeBound x cert ∧ v.Run A x cert t b) ∧
    ∀ x, L x = true ↔ ∃ cert t, cert.length ≤ certBound.eval x.length ∧
      t ≤ v.timeLimit timeBound x cert ∧ v.Run A x cert t true

/-- `P^A = NP^A`. -/
def PEqualsNPO (A : Oracle) : Prop := ∀ L, InNPO A L → InPO A L

/-- `P ⊆ P^A` for every oracle. -/
theorem inPO_of_inP (A : Oracle) {L : Language} (h : InP L) : InPO A L := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  refine ⟨liftMachine m, p, fun x => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hm x
  exact ⟨t, b, ht, (orun_lift_iff A m _ t b).mpr hr, hb⟩

/-- `P^∅ = P`: against a constant oracle, oracle machines are ordinary machines. -/
theorem inPO_const_iff (b : Bool) (L : Language) : InPO (fun _ => b) L ↔ InP L := by
  constructor
  · rintro ⟨m, p, hm⟩
    refine (polyDec_iff_inP L).mp ⟨lowerMachine b m, p, fun x => ?_⟩
    obtain ⟨t, r, ht, hr, hb⟩ := hm x
    exact ⟨t, r, ht, (run_lower_iff b m _ t r).mpr hr, hb⟩
  · exact inPO_of_inP _

/-- `P^A ⊆ NP^A` for every oracle. -/
theorem inNPO_of_inPO {A : Oracle} {L : Language} (h : InPO A L) : InNPO A L := by
  obtain ⟨m, p, hm⟩ := h
  refine ⟨.ignoreCertificate m, p, ⟨0, 0⟩, fun x _ _ => ?_, fun x => ?_⟩
  · obtain ⟨t, b, ht, hr, _⟩ := hm x
    exact ⟨t, b, ht, hr⟩
  · obtain ⟨t, b, ht, hr, hb⟩ := hm x
    constructor
    · intro hx
      exact ⟨[], t, Nat.zero_le _, ht, by rw [hb, hx] at hr; exact hr⟩
    · rintro ⟨_, t', _, _, hr'⟩
      rw [← hb, (orun_deterministic hr hr').2]

def liftVerifier : VerifierProgram → OVerifier
  | .ignoreCertificate m => .ignoreCertificate (liftMachine m)
  | .paired m => .paired (liftMachine m)

def OVerifier.lower (b : Bool) : OVerifier → VerifierProgram
  | .ignoreCertificate m => .ignoreCertificate (lowerMachine b m)
  | .paired m => .paired (lowerMachine b m)

theorem liftVerifier_run (A : Oracle) (v : VerifierProgram) (x cert : Word) (t : Nat) (r : Bool) :
    (liftVerifier v).Run A x cert t r ↔ v.Run x cert t r := by
  cases v <;> exact orun_lift_iff A _ _ t r

theorem liftVerifier_timeLimit (v : VerifierProgram) (p : Polynomial) (x cert : Word) :
    (liftVerifier v).timeLimit p x cert = v.timeLimit p x cert := by
  cases v <;> rfl

theorem lower_run (b : Bool) (v : OVerifier) (x cert : Word) (t : Nat) (r : Bool) :
    (v.lower b).Run x cert t r ↔ v.Run (fun _ => b) x cert t r := by
  cases v <;> exact run_lower_iff b _ _ t r

theorem lower_timeLimit (b : Bool) (v : OVerifier) (p : Polynomial) (x cert : Word) :
    (v.lower b).timeLimit p x cert = v.timeLimit p x cert := by
  cases v <;> rfl

/-- `NP ⊆ NP^A` for every oracle. -/
theorem inNPO_of_inNP (A : Oracle) {L : Language} (h : InNP L) : InNPO A L := by
  obtain ⟨N, rfl⟩ := h
  refine ⟨liftVerifier N.verifier, N.timeBound, N.certBound, fun x cert hc => ?_, fun x => ?_⟩
  · obtain ⟨t, b, ht, hr⟩ := N.terminates x cert hc
    exact ⟨t, b, by rw [liftVerifier_timeLimit]; exact ht, (liftVerifier_run A _ x cert t b).mpr hr⟩
  · rw [N.correct x]
    simp only [liftVerifier_timeLimit, liftVerifier_run]

/-- `NP^∅ = NP`. -/
theorem inNPO_const_iff (b : Bool) (L : Language) : InNPO (fun _ => b) L ↔ InNP L := by
  constructor
  · rintro ⟨v, tb, cb, hterm, hcorr⟩
    refine ⟨⟨L, v.lower b, tb, cb, fun x cert hc => ?_, fun x => ?_⟩, rfl⟩
    · obtain ⟨t, r, ht, hr⟩ := hterm x cert hc
      exact ⟨t, r, by rw [lower_timeLimit]; exact ht, (lower_run b v x cert t r).mpr hr⟩
    · rw [hcorr x]
      simp only [lower_timeLimit, lower_run]
  · exact inNPO_of_inNP _

/-- The unrelativized question is the instance of a constant (for example the
empty) oracle. -/
theorem pEqualsNPO_const_iff (b : Bool) : PEqualsNPO (fun _ => b) ↔ PEqualsNP := by
  constructor
  · intro h L hL
    exact (inPO_const_iff b L).mp (h L ((inNPO_const_iff b L).mpr hL))
  · intro h L hL
    exact (inPO_const_iff b L).mpr (h L ((inNPO_const_iff b L).mp hL))

/-- A relativizing proof of `P = NP` (one valid for every oracle) proves `P = NP`. -/
theorem pEqualsNP_of_all_oracles (h : ∀ A, PEqualsNPO A) : PEqualsNP :=
  (pEqualsNPO_const_iff false).mp (h _)

/-- A relativizing proof of `P ≠ NP` proves `P ≠ NP`. -/
theorem pNotEqualsNP_of_all_oracles (h : ∀ A, ¬ PEqualsNPO A) : PNotEqualsNP :=
  fun hP => h (fun _ => false) ((pEqualsNPO_const_iff false).mpr hP)

/-! ## Baker–Gill–Solovay, stated in this model -/

/-- **Known theorem, not mechanised here** (Baker, Gill, Solovay, "Relativizations
of the P =? NP question", SIAM J. Comput. 4(4), 1975): there is an oracle `A` with
`P^A = NP^A` (for example a PSPACE-complete language). -/
def BGSCollapse : Prop := ∃ A : Oracle, PEqualsNPO A

/-- **Known theorem, not mechanised here** (Baker, Gill, Solovay 1975): there is an
oracle `B` with `P^B ≠ NP^B`. Its query-complexity core is `oracle_adversary`. -/
def BGSSeparation : Prop := ∃ B : Oracle, ¬ PEqualsNPO B

/-- **The barrier.** Given BGS, neither answer to P vs NP holds relative to every
oracle, so no argument that is valid for every oracle settles P vs NP. -/
theorem bgs_no_uniform_answer (h1 : BGSCollapse) (h2 : BGSSeparation) :
    ¬ (∀ A, PEqualsNPO A) ∧ ¬ (∀ A, ¬ PEqualsNPO A) := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  exact ⟨fun h => hB (h B), fun h => h A hA⟩

/-! ## The diagonal half of the time hierarchy, in the machine model -/

open Classical in
/-- The diagonal language of an injectively coded family with acceptance
relation `Acc`: `w` is in it unless `w` is the code of a member accepting `w`. -/
noncomputable def diagLang {M : Type} (e : M → Word) (Acc : M → Word → Prop) : Language :=
  fun w => decide (¬ ∃ m, e m = w ∧ Acc m w)

/-- **Diagonal core.** No member of the family accepts exactly `diagLang`. -/
theorem diagonal_core {M : Type} (e : M → Word) (he : ∀ a b, e a = e b → a = b)
    (Acc : M → Word → Prop) (m : M) : ¬ ∀ w, Acc m w ↔ diagLang e Acc w = true := by
  intro h
  have hw := h (e m)
  by_cases ha : Acc m (e m)
  · have hd := hw.mp ha
    simp only [diagLang, decide_eq_true_eq] at hd
    exact hd ⟨m, rfl, ha⟩
  · have hd : ¬ diagLang e Acc (e m) = true := fun hd => ha (hw.mpr hd)
    simp only [diagLang, decide_eq_true_eq, Classical.not_not] at hd
    obtain ⟨m', hm', ha'⟩ := hd
    rw [he m' m hm'] at ha'
    exact ha ha'

/-- Clocked acceptance: `m` accepts `w` within `p(|w|)` steps. -/
def AcceptsWithin (m : Machine) (p : Polynomial) (w : Word) : Prop :=
  ∃ t, t ≤ p.eval w.length ∧ Run m (initial w) t true

/-- The clocked diagonal language for the time bound `p`. -/
noncomputable def DiagWithin (p : Polynomial) : Language :=
  diagLang encMachine (fun m w => AcceptsWithin m p w)

theorem acceptsWithin_iff_of_decidesWithin {m : Machine} {p : Polynomial} {L : Language}
    (h : DecidesWithin m p L) (w : Word) : AcceptsWithin m p w ↔ L w = true := by
  obtain ⟨t, b, ht, hr, hb⟩ := h w
  constructor
  · rintro ⟨t', _, hr'⟩
    rw [← hb, (run_deterministic hr hr').2]
  · intro hL
    exact ⟨t, ht, by rw [hb, hL] at hr; exact hr⟩

/-- **Diagonal half of the deterministic time hierarchy (proved).** No machine
decides `DiagWithin p` within the time bound `p`. -/
theorem diagWithin_not_decidedWithin (p : Polynomial) :
    ¬ ∃ m, DecidesWithin m p (DiagWithin p) := by
  rintro ⟨m, hm⟩
  exact diagonal_core encMachine (fun _ _ h => encMachine_injective h)
    (fun m w => AcceptsWithin m p w) m (acceptsWithin_iff_of_decidesWithin hm)

/-- **Known theorem, not mechanised here** (clocked universal simulation:
Hartmanis–Stearns, "On the computational complexity of algorithms", Trans. AMS
117, 1965; Hennie–Stearns, J. ACM 13(4), 1966): for each polynomial `p`, a
machine can check whether `w` codes a machine `m` and simulate `m` on `w` for
`p(|w|)` steps in polynomial time, so `DiagWithin p` is in P. -/
def UniversalSimulation : Prop := ∀ p : Polynomial, InP (DiagWithin p)

/-- **The deterministic time hierarchy for polynomial bounds, in the machine
model:** no single polynomial bounds the running time of all of P. -/
def TimeHierarchy : Prop :=
  ∀ p : Polynomial, ∃ L : Language, InP L ∧ ¬ ∃ m, DecidesWithin m p L

/-- The time hierarchy follows from the proved diagonal half and universal simulation. -/
theorem timeHierarchy_of_universalSimulation (h : UniversalSimulation) : TimeHierarchy :=
  fun p => ⟨DiagWithin p, h p, diagWithin_not_decidedWithin p⟩

/-- Consequence: P has no uniform polynomial time bound. -/
theorem no_uniform_bound_of_timeHierarchy (h : TimeHierarchy) :
    ¬ ∃ p : Polynomial, ∀ L, InP L → ∃ m, DecidesWithin m p L := by
  rintro ⟨p, hp⟩
  obtain ⟨L, hL, hn⟩ := h p
  exact hn (hp L hL)

/-! ## The diagonal half relative to every oracle -/

def encOInstruction : OInstruction → Word
  | .base i => false :: encInstruction i
  | .query yes no => true :: (encNat yes ++ encNat no)

theorem encOInstruction_prefixFree : PrefixFree encOInstruction := by
  intro a b r s h
  cases a with
  | base i =>
    cases b with
    | base j =>
      simp only [encOInstruction, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := encInstruction_prefixFree _ _ _ _ h
      exact ⟨by rw [h1], h2⟩
    | query _ _ => simp [encOInstruction] at h
  | query y n =>
    cases b with
    | base _ => simp [encOInstruction] at h
    | query y' n' =>
      simp only [encOInstruction, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨h1, h2⟩ := encNat_prefixFree _ _ _ _ h
      obtain ⟨h3, h4⟩ := encNat_prefixFree _ _ _ _ h2
      exact ⟨by rw [h1, h3], h4⟩

/-- The code of an oracle machine. -/
def encOMachine (m : OMachine) : Word := encList (encList encOInstruction) m.program

theorem encOMachine_injective (m m' : OMachine) (h : encOMachine m = encOMachine m') : m = m' := by
  have := (encList_prefixFree (encList_prefixFree encOInstruction_prefixFree)) m.program
    m'.program [] [] (by simpa [encOMachine] using h)
  cases m; cases m'
  simp only at this
  rw [this.1]

/-- Clocked acceptance relative to the oracle `A`. -/
def OAcceptsWithin (A : Oracle) (m : OMachine) (p : Polynomial) (w : Word) : Prop :=
  ∃ t, t ≤ p.eval w.length ∧ ORun A m (initial w) t true

/-- The clocked diagonal language relative to `A`. -/
noncomputable def DiagWithinO (A : Oracle) (p : Polynomial) : Language :=
  diagLang encOMachine (fun m w => OAcceptsWithin A m p w)

/-- **The diagonal half relativizes (proved for every oracle).** No oracle machine
decides `DiagWithinO A p` with oracle `A` within `p`. -/
theorem diagWithinO_not_decidedWithin (A : Oracle) (p : Polynomial) :
    ¬ ∃ m, ODecidesWithin A m p (DiagWithinO A p) := by
  rintro ⟨m, hm⟩
  unfold DiagWithinO at hm
  refine diagonal_core encOMachine encOMachine_injective (fun m w => OAcceptsWithin A m p w) m
    fun w => ?_
  obtain ⟨t, b, ht, hr, hb⟩ := hm w
  constructor
  · rintro ⟨t', _, hr'⟩
    rw [← hb, (orun_deterministic hr hr').2]
  · intro hL
    exact ⟨t, ht, by rw [hb, hL] at hr; exact hr⟩

/-- The time hierarchy relative to `A`. -/
def TimeHierarchyO (A : Oracle) : Prop :=
  ∀ p : Polynomial, ∃ L : Language, InPO A L ∧ ¬ ∃ m, ODecidesWithin A m p L

/-- **Known theorem, not mechanised here** (the universal simulation of
Hartmanis–Stearns 1965 makes the same queries as the simulated machine; see Baker,
Gill, Solovay 1975, Section 1): for each oracle `A` and polynomial `p`,
`DiagWithinO A p` is in `P^A`. -/
def UniversalSimulationO : Prop := ∀ (A : Oracle) (p : Polynomial), InPO A (DiagWithinO A p)

/-- The time hierarchy holds relative to every oracle: it is a relativizing theorem,
which is why it cannot settle P vs NP (`bgs_no_uniform_answer`). -/
theorem timeHierarchyO_of_universalSimulationO (h : UniversalSimulationO) :
    ∀ A, TimeHierarchyO A :=
  fun A p => ⟨DiagWithinO A p, h A p, diagWithinO_not_decidedWithin A p⟩

/-! ## Time classes and the nondeterministic time hierarchy

`T : Nat → Nat` is an arbitrary time function; `c` absorbs constant factors. -/

/-- `L ∈ DTIME(T)`: a machine decides `L` within `c·T(|x|) + c` steps. -/
def InDTIME (T : Nat → Nat) (L : Language) : Prop :=
  ∃ (m : Machine) (c : Nat), ∀ x, ∃ t b, t ≤ c * T x.length + c ∧ Run m (initial x) t b ∧ b = L x

/-- `L ∈ NTIME(T)`, in the verifier form of `Complexity.ClassNP`: a machine reading
`pairedInput x cert` halts within `c·T(|x|) + c` steps on every certificate of length
at most `c·T(|x|) + c`, and `x ∈ L` iff some such certificate is accepted. -/
def InNTIME (T : Nat → Nat) (L : Language) : Prop :=
  ∃ (m : Machine) (c : Nat),
    (∀ x cert, cert.length ≤ c * T x.length + c →
      ∃ t b, t ≤ c * T x.length + c ∧ Run m (pairedInput x cert) t b) ∧
    ∀ x, L x = true ↔ ∃ cert t, cert.length ≤ c * T x.length + c ∧
      t ≤ c * T x.length + c ∧ Run m (pairedInput x cert) t true

/-- A separation of nondeterministic time classes: `NTIME(T₂) ⊄ NTIME(T₁)`. -/
def NTimeHierarchyGap (T₁ T₂ : Nat → Nat) : Prop := ∃ L, InNTIME T₂ L ∧ ¬ InNTIME T₁ L

/-- **Known theorem, not mechanised here** (nondeterministic time hierarchy: Cook,
"A hierarchy for nondeterministic time complexity", JCSS 7(4), 1973;
Seiferas–Fischer–Meyer, J. ACM 25(1), 1978; Žák, TCS 21(3), 1983), in the form
used by Williams' ACC lower bound: `NTIME(2^n) ⊄ NTIME(2^n / (n+1)^k)` for every
`k ≥ 3`. The published proofs are for multitape machines; the polynomial gap
`(n+1)^k` with `k ≥ 3` leaves room for the `O(|M|·T)` overhead of one-tape
universal simulation in this one-tape verifier model. -/
def NTimeHierarchy : Prop :=
  ∀ k : Nat, 3 ≤ k → NTimeHierarchyGap (fun n => 2 ^ n / (n + 1) ^ k) (fun n => 2 ^ n)

open Classical in
/-- The language accepted by the verifier `x.1` with constant `x.2.coefficient`. -/
noncomputable def ntimeLanguage (T : Nat → Nat) (x : Machine × Polynomial) : Language :=
  fun w => decide (∃ cert t, cert.length ≤ x.2.coefficient * T w.length + x.2.coefficient ∧
    t ≤ x.2.coefficient * T w.length + x.2.coefficient ∧ Run x.1 (pairedInput w cert) t true)

/-- Non-vacuity: every `NTIME(T)` misses some language. -/
theorem exists_not_inNTIME (T : Nat → Nat) : ∃ L, ¬ InNTIME T L := by
  classical
  obtain ⟨L, hL⟩ := exists_language_not_in_family encMachinePoly encMachinePoly_injective
    (ntimeLanguage T)
  refine ⟨L, fun ⟨m, c, _, hc⟩ => hL (m, ⟨c, 0⟩) (funext fun w => ?_)⟩
  simp only [ntimeLanguage]
  cases hw : L w with
  | true => exact decide_eq_true ((hc w).mp hw)
  | false =>
    exact decide_eq_false fun h => by rw [(hc w).mpr h] at hw; cases hw

/-- Non-vacuity: every `DTIME(T)` misses some language. -/
theorem exists_not_inDTIME (T : Nat → Nat) : ∃ L, ¬ InDTIME T L := by
  classical
  obtain ⟨L, hL⟩ := exists_language_not_in_family encMachinePoly encMachinePoly_injective
    (fun x w => decide (∃ t, t ≤ x.2.coefficient * T w.length + x.2.coefficient ∧
      Run x.1 (initial w) t true))
  refine ⟨L, fun ⟨m, c, hm⟩ => hL (m, ⟨c, 0⟩) (funext fun w => ?_)⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hm w
  cases hw : L w with
  | true => exact decide_eq_true ⟨t, ht, by rw [hb, hw] at hr; exact hr⟩
  | false =>
    refine decide_eq_false fun ⟨t', _, hr'⟩ => ?_
    rw [(run_deterministic hr hr').2, hw] at hb
    cases hb

end Issue532.Idea16
