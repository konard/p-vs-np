import proofs.experiments.issue532.lean.Idea14
open Issue532.Idea14

/-- (a) `PolyDec` holds for every language (reviewer's example). -/
theorem idea14_polyDec_trivial {α : Type} (sz : α → Nat) (L : α → Bool) : PolyDec sz L :=
  ⟨L, fun _ => 0, 0, 0, fun _ => rfl, fun _ => Nat.zero_le _⟩

/-- The one-seed algorithm `A x _ := L x` is one-sided. -/
theorem oneSided_trivial {α : Type} (L : α → Bool) :
    OneSided L (fun x _ => L x) (fun _ => 1) := by
  intro x
  refine ⟨Nat.one_pos, fun h _ => h, fun h => ?_⟩
  simp [cnt, sumTo, h]

/-- (a) `RPDecider` (hence the obligation `NPinRP`) holds for every language:
seed length `r := 0` (one seed), and the time `T` is an unconstrained witness. -/
theorem idea14_NPinRP_trivial {α : Type} (sz : α → Nat) (L : α → Bool) : NPinRP sz L := by
  refine ⟨fun x _ => L x, fun _ => 0, fun _ => 0, 1, 0, ?_, fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩⟩
  simpa using oneSided_trivial L

/-- (a) `PolySeedRP` holds for every language. -/
theorem idea14_polySeedRP_trivial {α : Type} (sz : α → Nat) (L : α → Bool) : PolySeedRP sz L :=
  ⟨fun x _ => L x, fun _ => 1, fun _ => 0, 1, 0, oneSided_trivial L,
    fun _ => ⟨by simp, Nat.zero_le _⟩⟩

/-- (a) `SeedCompression` holds for every language (its conclusion is trivially true). -/
theorem idea14_seedCompression_trivial {α : Type} (sz : α → Nat) (L : α → Bool) :
    SeedCompression sz L :=
  fun _ => idea14_polySeedRP_trivial sz L
