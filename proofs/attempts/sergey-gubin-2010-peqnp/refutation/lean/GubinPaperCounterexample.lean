import Std

/-!
  A concrete counterexample to Gubin, cs/0610042v3, Theorem 1.2.
  Indices below are zero-based. `PaperFeasible` transcribes (1.8) and (1.9)
  for six vertices. The graph is two disjoint directed 3-cycles.
-/

namespace GubinPaperCounterexample

abbrev V := Fin 6

def next (i j : V) : Bool := decide (j.val = (i.val + 1) % 6)

def edge (a b : V) : Bool :=
  decide ((a.val = 0 ∧ b.val = 1) ∨
    (a.val = 1 ∧ b.val = 2) ∨
    (a.val = 2 ∧ b.val = 0) ∨
    (a.val = 3 ∧ b.val = 4) ∨
    (a.val = 4 ∧ b.val = 5) ∨
    (a.val = 5 ∧ b.val = 3))

def group (a : V) : Bool := a.val < 3

def compatible (i j a b : V) : Bool :=
  (!next i j || edge a b) && (!next j i || edge b a)

def sum6 (f : V → Rat) : Rat :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5

/-- Gubin's (1.8) and (1.9), including rational nonnegativity. -/
def PaperFeasible (x : V → V → V → V → Rat) (y : V → V → Rat) : Prop :=
  (∀ i j a b, i ≠ j → a ≠ b → x i j a b = x j i b a ∧ 0 ≤ x i j a b) ∧
  (∀ i j b, i ≠ j →
    sum6 (fun a => if a = b then 0 else x i j a b) = y j b) ∧
  (∀ j a b, a ≠ b →
    sum6 (fun i => if i = j then 0 else x i j a b) = y j b) ∧
  (∀ j, sum6 (y j) = 1 ∧ ∀ b, 0 ≤ y j b) ∧
  (∀ i j a b, i ≠ j → a ≠ b → compatible i j a b = false → x i j a b = 0)

def y (_ _ : V) : Rat := 1 / 6

def x (i j a b : V) : Rat :=
  if i = j ∨ a = b then 0
  else if next i j then if edge a b then 1 / 6 else 0
  else if next j i then if edge b a then 1 / 6 else 0
  else if group a != group b then 1 / 18 else 0

theorem witness_feasible : PaperFeasible x y := by
  unfold PaperFeasible
  decide +kernel

def succ (i : V) : V := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

/-- A Hamiltonian tour lists every vertex and follows directed edges. -/
def HasTour : Prop :=
  ∃ p : V → V,
    (∀ i j, p i = p j → i = j) ∧
    (∀ a, ∃ i, p i = a) ∧
    (∀ i, edge (p i) (p (succ i)) = true)

private theorem edge_same_group :
    ∀ a b : V, edge a b = true → group a = group b := by decide

theorem no_hamiltonian_tour : ¬HasTour := by
  intro h
  obtain ⟨p, _, hsurj, hcycle⟩ := h
  have hs (i : V) : group (p i) = group (p (succ i)) :=
    edge_same_group _ _ (hcycle i)
  have h01 : group (p 0) = group (p 1) := by simpa [succ] using hs 0
  have h12 : group (p 1) = group (p 2) := by simpa [succ] using hs 1
  have h23 : group (p 2) = group (p 3) := by simpa [succ] using hs 2
  have hsucc3 : succ 3 = 4 := by decide
  have hsucc4 : succ 4 = 5 := by decide
  have h34 : group (p 3) = group (p 4) := by simpa [hsucc3] using hs 3
  have h45 : group (p 4) = group (p 5) := by simpa [hsucc4] using hs 4
  have hcases : ∀ i : V, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  have hall (i : V) : group (p i) = group (p 0) := by
    rcases hcases i with h | h | h | h | h | h <;> subst i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
    · exact ((h01.trans h12).trans h23).symm
    · exact (((h01.trans h12).trans h23).trans h34).symm
    · exact ((((h01.trans h12).trans h23).trans h34).trans h45).symm
  obtain ⟨i0, hi0⟩ := hsurj 0
  obtain ⟨i3, hi3⟩ := hsurj 3
  have hg : group (p i0) = group (p i3) := (hall i0).trans (hall i3).symm
  rw [hi0, hi3] at hg
  have hneq : group (0 : V) ≠ group (3 : V) := by decide
  exact hneq hg

/-- Equations (1.8) and (1.9) have a point despite the absence of a tour.
    This contradicts the claimed LP/tour correspondence in Theorem 1.2. -/
theorem paper_correspondence_fails : PaperFeasible x y ∧ ¬HasTour :=
  ⟨witness_feasible, no_hamiltonian_tour⟩

/-- The LP feasibility-to-tour implication used after Theorem 1.2 is false. -/
theorem claimed_soundness_false :
    ¬(∀ x y, PaperFeasible x y → HasTour) := by
  intro h
  exact no_hamiltonian_tour (h x y witness_feasible)

end GubinPaperCounterexample
