import proofs.complexity.lean.Complexity

/-! Shared NAND circuit definitions, independent of the machine compiler. -/

namespace Issue532.Circuits
open Complexity

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
positive input length.

Length `0` is excluded on purpose. A well-formed circuit on `0` inputs has no
gates (`WF 0 C` forces `C = []`), so its output is the constant `false`. If
length `0` counted, every language with `L [] = true` (SAT among them, since
the empty CNF is satisfiable) would be outside P/poly for a trivial reason,
and `PSubsetPPoly` would be false. One word per length changes no asymptotic
notion. -/
def InPPoly (L : Language) : Prop :=
  ∃ p : Polynomial, ∀ n, 0 < n → ∃ C : Circuit, C.length ≤ p.eval n ∧ CircuitDecides n C L

def PSubsetPPoly : Prop := ∀ L : Language, InP L → InPPoly L

theorem wire_append_self (x : List Bool) (b : Bool) : wire (x ++ [b]) x.length = b := by
  simp [wire]

theorem wire_append_lt (x : List Bool) (b : Bool) (i : Nat) (h : i < x.length) :
    wire (x ++ [b]) i = wire x i := by
  simp [wire, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

end Issue532.Circuits
