import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532: a shared circuit model and the bridge to the machine model

Circuit lower bounds in the idea files are stated for the machine-model
language `Issue532.Machines.SAT`, over one concrete circuit model: NAND
straight-line programs. The model is honest: a circuit is a list of gates, its
size is the number of gates, and its output is computed by `output`.

* `Circuit`, `output`, `WF`: NAND straight-line programs on `n` input wires.
* `InPPoly`, `SuperpolyLowerBound`, `superpoly_iff_not_inPPoly`: the class
  P/poly and a superpolynomial circuit lower bound, which are complementary.
* `PSubsetPPoly`: every language in P has polynomial-size circuits
  (Savage 1972; Pippenger–Fischer 1979; Arora–Barak Theorem 6.6). It is a
  known theorem that this file does **not** prove; every use is an explicit
  hypothesis named `PSubsetPPoly`.
* `pNotEqualsNP_of_superpoly_sat`: under `SATInNP` and `PSubsetPPoly`, a
  superpolynomial circuit lower bound for SAT gives P ≠ NP.
-/

namespace Issue532.Circuits

open Complexity Issue532.Machines

/-- Gate `(i, j)` appends the NAND of wires `i` and `j`. -/
abbrev Circuit := List (Nat × Nat)

def wire (w : List Bool) (i : Nat) : Bool := w.getD i false

/-- All wire values: the inputs followed by one wire per gate. -/
def wires (w : List Bool) : Circuit → List Bool
  | [] => w
  | (i, j) :: C => wires (w ++ [!(wire w i && wire w j)]) C

/-- The output is the last wire. -/
def output (x : Word) (C : Circuit) : Bool := (wires x C).getLastD false

/-- Gate `k` only reads the `N` earlier wires. -/
def WFfrom : Nat → Circuit → Prop
  | _, [] => True
  | N, (i, j) :: C => i < N ∧ j < N ∧ WFfrom (N + 1) C

/-- A well-formed circuit on `n` inputs. -/
def WF (n : Nat) (C : Circuit) : Prop := WFfrom n C

/-- `C` is a well-formed circuit on `n` inputs that agrees with `L` on every
word of length `n`. -/
def CircuitDecides (n : Nat) (C : Circuit) (L : Language) : Prop :=
  WF n C ∧ ∀ x : Word, x.length = n → output x C = L x

/-- The class P/poly: `L` has circuits with polynomially many gates at every
input length. -/
def InPPoly (L : Language) : Prop :=
  ∃ p : Polynomial, ∀ n, ∃ C : Circuit, C.length ≤ p.eval n ∧ CircuitDecides n C L

/-- A superpolynomial circuit lower bound: for every polynomial some input
length defeats every circuit of that size. -/
def SuperpolyLowerBound (L : Language) : Prop :=
  ∀ p : Polynomial, ∃ n, ∀ C : Circuit, C.length ≤ p.eval n → WF n C →
    ∃ x : Word, x.length = n ∧ output x C ≠ L x

theorem superpoly_iff_not_inPPoly (L : Language) : SuperpolyLowerBound L ↔ ¬ InPPoly L := by
  constructor
  · rintro h ⟨p, hp⟩
    obtain ⟨n, hn⟩ := h p
    obtain ⟨C, hl, hw, hc⟩ := hp n
    obtain ⟨x, hx, hne⟩ := hn C hl hw
    exact hne (hc x hx)
  · intro h p
    apply Classical.byContradiction
    intro hno
    apply h
    refine ⟨p, fun n => ?_⟩
    apply Classical.byContradiction
    intro hC
    apply hno
    refine ⟨n, fun C hl hw => ?_⟩
    apply Classical.byContradiction
    intro hx
    apply hC
    refine ⟨C, hl, hw, fun x hlen => ?_⟩
    apply Classical.byContradiction
    intro hne
    exact hx ⟨x, hlen, hne⟩

/-- **Known theorem, not mechanised here.** Every language decided by a
polynomial-time `Complexity.Machine` has polynomial-size NAND circuits
(Savage 1972; Pippenger–Fischer 1979; Arora–Barak Theorem 6.6). The missing
part is the tableau construction for this machine model. -/
def PSubsetPPoly : Prop := ∀ L : Language, InP L → InPPoly L

/-- A language outside P/poly is outside P, given `PSubsetPPoly`. -/
theorem not_inP_of_not_inPPoly (hP : PSubsetPPoly) {L : Language} (h : ¬ InPPoly L) :
    ¬ InP L :=
  fun hL => h (hP L hL)

/-- **Bridge.** A superpolynomial circuit lower bound for SAT gives P ≠ NP,
using the membership half of Cook–Levin and `PSubsetPPoly`. -/
theorem pNotEqualsNP_of_superpoly_sat (mem : SATInNP) (hP : PSubsetPPoly)
    (h : SuperpolyLowerBound SAT) : PNotEqualsNP := fun hEq =>
  not_inP_of_not_inPPoly hP ((superpoly_iff_not_inPPoly SAT).mp h) (inP_sat_of_pEqualsNP mem hEq)

/-- The same bridge for any NP language. -/
theorem pNotEqualsNP_of_superpoly (hP : PSubsetPPoly) {L : Language} (mem : InNP L)
    (h : SuperpolyLowerBound L) : PNotEqualsNP := fun hEq =>
  not_inP_of_not_inPPoly hP ((superpoly_iff_not_inPPoly L).mp h) (hEq L mem)

end Issue532.Circuits
