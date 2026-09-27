/-!
# Issue #532, Idea 05: greedy optimization

Summary. We model one decision step followed by a forced continuation. An
*option* is a pair `(first, rest)`. `first` is the cost visible when the choice
is made, and `rest` is the cost that the choice forces later. Greedy picks the
option with the smallest visible cost. The optimum picks the smallest total.

Machine-checked, for all parameters:
* `argminBy_mem`, `argminBy_le`: the generic selection rule is correct.
* `optCost_le`, `optCost_achieved`, `optCost_le_greedyCost`: the optimum is a
  lower bound that is attained, and greedy is never better than it.
* `greedy_optimal_of_uniform_continuation`: if every option forces the same
  continuation cost, greedy is optimal.
* `trap_greedyCost`, `trap_optCost`, `greedy_ratio_unbounded`: for every `r`
  there is an instance where greedy costs more than `r` times the optimum.
* `greedyPicks_valid`, `greedyPicks_optimal`: when the decisions are
  independent (choose one element from each group, a partition matroid), the
  greedy choice minimises the total.

Verdict: refuted as a route (general theorem). Greedy is exact when the
decisions separate (matroid-like structure) and has unbounded error as soon
as an early choice constrains later costs.
-/

namespace Issue532.Idea05

/-! ## Generic selection by a key -/

/-- Return the element of `o :: os` with the smallest key `f`
(the earliest one on ties). -/
def argminBy {α : Type} (f : α → Nat) : α → List α → α
  | o, [] => o
  | o, p :: ps => if f (argminBy f p ps) < f o then argminBy f p ps else o

/-- The selected element is one of the candidates. -/
theorem argminBy_mem {α : Type} (f : α → Nat) (o : α) (os : List α) :
    argminBy f o os ∈ o :: os := by
  induction os generalizing o with
  | nil => simp [argminBy]
  | cons p ps ih =>
    simp only [argminBy]
    split
    · exact List.mem_cons_of_mem _ (ih p)
    · simp

/-- The selected element has the smallest key among the candidates. -/
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

/-! ## Two-stage instances -/

/-- Total cost of an option `(first, rest)`. -/
def total (o : Nat × Nat) : Nat := o.1 + o.2

/-- Greedy looks only at the visible first-stage cost. -/
def greedyChoice (o : Nat × Nat) (os : List (Nat × Nat)) : Nat × Nat :=
  argminBy (fun p => p.1) o os

/-- Total cost paid by greedy. -/
def greedyCost (o : Nat × Nat) (os : List (Nat × Nat)) : Nat :=
  total (greedyChoice o os)

/-- Optimal total cost. -/
def optCost (o : Nat × Nat) (os : List (Nat × Nat)) : Nat :=
  total (argminBy total o os)

/-- The optimum is at most the total of every option. -/
theorem optCost_le (o : Nat × Nat) (os : List (Nat × Nat)) :
    ∀ p, p ∈ o :: os → optCost o os ≤ total p :=
  argminBy_le total o os

/-- The optimum is attained by some option. -/
theorem optCost_achieved (o : Nat × Nat) (os : List (Nat × Nat)) :
    ∃ p, p ∈ o :: os ∧ total p = optCost o os :=
  ⟨argminBy total o os, argminBy_mem total o os, rfl⟩

/-- Greedy picks a real option. -/
theorem greedyChoice_mem (o : Nat × Nat) (os : List (Nat × Nat)) :
    greedyChoice o os ∈ o :: os :=
  argminBy_mem _ o os

/-- Greedy is never better than the optimum. -/
theorem optCost_le_greedyCost (o : Nat × Nat) (os : List (Nat × Nat)) :
    optCost o os ≤ greedyCost o os :=
  optCost_le o os _ (greedyChoice_mem o os)

/-- If every option forces the same continuation cost `c`, greedy is optimal. -/
theorem greedy_optimal_of_uniform_continuation (o : Nat × Nat) (os : List (Nat × Nat))
    (c : Nat) (hc : ∀ p, p ∈ o :: os → p.2 = c) :
    greedyCost o os = optCost o os := by
  apply Nat.le_antisymm
  · obtain ⟨p, hp, hpt⟩ := optCost_achieved o os
    have hle := argminBy_le (fun q => q.1) o os p hp
    have hg := hc _ (greedyChoice_mem o os)
    have hpc := hc p hp
    rw [← hpt]
    unfold greedyCost greedyChoice total at *
    omega
  · exact optCost_le_greedyCost o os

/-! ## The trap family -/

/-- Greedy on the trap instance `[(1, k), (2, 0)]` pays `k + 1`. -/
theorem trap_greedyCost (k : Nat) : greedyCost (1, k) [(2, 0)] = k + 1 := by
  simp [greedyCost, greedyChoice, argminBy, total]
  omega

/-- The optimum of the trap instance is `2` whenever `k ≥ 1`. -/
theorem trap_optCost (k : Nat) (hk : 1 ≤ k) : optCost (1, k) [(2, 0)] = 2 := by
  unfold optCost
  by_cases h : 2 < 1 + k
  · simp [argminBy, total, h]
  · simp [argminBy, total, h]; omega

/-- Greedy has unbounded approximation ratio: for every `r` there is an
instance with positive optimum where greedy costs more than `r` times the
optimum. -/
theorem greedy_ratio_unbounded (r : Nat) :
    ∃ o os, 0 < optCost o os ∧ r * optCost o os < greedyCost o os := by
  refine ⟨(1, 2 * r + 1), [(2, 0)], ?_, ?_⟩
  · rw [trap_optCost _ (by omega)]; omega
  · rw [trap_optCost _ (by omega), trap_greedyCost]; omega

/-! ## Independent decisions: greedy is exact -/

/-- `Picks gs xs`: `xs` chooses one element from each group of `gs`. A group
`(h, t)` is the nonempty list `h :: t`. -/
inductive Picks : List (Nat × List Nat) → List Nat → Prop
  | nil : Picks [] []
  | cons {h : Nat} {t : List Nat} {gs : List (Nat × List Nat)} {xs : List Nat} {x : Nat} :
      x ∈ h :: t → Picks gs xs → Picks ((h, t) :: gs) (x :: xs)

/-- Greedy: take the smallest element of every group. -/
def greedyPicks : List (Nat × List Nat) → List Nat
  | [] => []
  | (h, t) :: gs => argminBy (fun x => x) h t :: greedyPicks gs

/-- Sum of a list of costs. -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- The greedy choice is feasible. -/
theorem greedyPicks_valid (gs : List (Nat × List Nat)) : Picks gs (greedyPicks gs) := by
  induction gs with
  | nil => exact Picks.nil
  | cons g gs ih =>
    obtain ⟨h, t⟩ := g
    exact Picks.cons (argminBy_mem _ h t) ih

/-- The greedy choice has minimum total cost among all feasible choices. -/
theorem greedyPicks_optimal (gs : List (Nat × List Nat)) (xs : List Nat)
    (hxs : Picks gs xs) : sumList (greedyPicks gs) ≤ sumList xs := by
  induction hxs with
  | nil => exact Nat.le_refl _
  | @cons h t gs xs x hx _ ih =>
    have := argminBy_le (fun y => y) h t x hx
    simp only [greedyPicks, sumList] at *
    omega

end Issue532.Idea05
