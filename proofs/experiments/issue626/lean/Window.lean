import proofs.experiments.issue568.lean.Tableau

/-! A shrinking, blank-padded tape window. Each charged step consumes at most
one cell of lookahead on either side. The initial width is `n + clock + 1`;
this is deliberately a coarse bound, shared with the bounded tableau. -/

namespace Issue626.Window
open Complexity Issue568.Tableau

def pad (k : Nat) (l : List Symbol) : List Symbol :=
  match k, l with
  | 0, _ => []
  | k + 1, [] => .blank :: pad k []
  | k + 1, a :: rest => a :: pad k rest

@[simp] theorem pad_length (k : Nat) (l : List Symbol) : (pad k l).length = k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => cases l <;> simp [pad, ih]

theorem pad_pad {k w : Nat} (h : k ≤ w) (l : List Symbol) :
    pad k (pad w l) = pad k l := by
  induction k generalizing w l with
  | zero => rfl
  | succ k ih =>
      cases w with
      | zero => omega
      | succ w => cases l <;> simp only [pad, List.cons.injEq] <;>
          exact ⟨trivial, ih (by omega) _⟩

theorem pad_cons_pad {k w : Nat} (h : k ≤ w + 1) (a : Symbol) (l : List Symbol) :
    pad k (a :: pad w l) = pad k (a :: l) := by
  cases k with
  | zero => rfl
  | succ k => simp only [pad]; exact congrArg (List.cons a) (pad_pad (by omega) l)

theorem pad_blank (k : Nat) : pad k [.blank] = pad k [] := by
  cases k <;> rfl

def window (k : Nat) (c : Config) : Config :=
  ⟨c.state, pad k c.left, c.head, pad k c.right⟩

/-- Moving in a padded window and then discarding one boundary cell agrees
with moving on the unbounded tape and taking the smaller window. This
includes moving into a previously unrepresented blank cell. -/
theorem window_move (k : Nat) (c : Config) (q : Nat) (s : Symbol) (d : Direction) :
    window k (moveHead (window (k + 1) c) q s d) =
      window k (moveHead c q s d) := by
  cases c with
  | mk state l head r =>
      cases d <;> cases l <;> cases r <;>
        simp only [window, pad, moveHead]
      all_goals
        congr 1
        all_goals first
          | exact pad_pad (by omega) _
          | exact (pad_cons_pad (by omega) _ _).trans (pad_blank k)
          | exact pad_cons_pad (by omega) _ _
          | cases k with
            | zero => rfl
            | succ k =>
                simp only [pad]
                congr 1
                first
                  | change pad k (pad (k + 2) []) = pad k []
                    exact pad_pad (by omega) []
                  | exact pad_cons_pad (k := k) (w := k) (by omega) _ _
                  | exact pad_cons_pad (k := k) (w := k + 1) (by omega) _ _

def next (m : Machine) (k : Nat) : Bool ⊕ Config → Bool ⊕ Config
  | .inl b => .inl b
  | .inr c => match step m c with
      | .inl b => .inl b
      | .inr d => .inr (window k d)

/-- Halted rows are absorbing; the final halt still costs one instruction. -/
def runWindow (m : Machine) : Nat → Nat → Bool ⊕ Config → Bool ⊕ Config
  | 0, _, c => c
  | t + 1, k, c => runWindow m t (k - 1) (next m (k - 1) c)

theorem window_step (m : Machine) (k : Nat) (c : Config) :
    next m k (.inr (window (k + 1) c)) =
      match step m c with
      | .inl b => .inl b
      | .inr d => .inr (window k d) := by
  simp only [next, step, window]
  cases hi : m.instruction c.state c.head with
  | halt b => rfl
  | move q s d => exact congrArg Sum.inr (window_move k c q s d)

theorem runWindow_halt (m : Machine) (t k : Nat) (b : Bool) :
    runWindow m t k (.inl b) = .inl b := by
  induction t generalizing k with
  | zero => rfl
  | succ t ih => exact ih _

theorem runWindow_correct {m : Machine} {c : Config} {t : Nat} {b : Bool}
    (hr : Run m c t b) : ∀ clock k, t ≤ clock → clock ≤ k →
      runWindow m clock k (.inr (window k c)) = .inl b := by
  induction hr with
  | halt hs =>
      intro clock k ht hk
      cases clock with
      | zero => omega
      | succ clock =>
          cases k with
          | zero => omega
          | succ k =>
              simp only [runWindow, Nat.add_sub_cancel, window_step, hs]
              exact runWindow_halt _ _ _ _
  | next hs _ ih =>
      intro clock k ht hk
      cases clock with
      | zero => omega
      | succ clock =>
          cases k with
          | zero => omega
          | succ k =>
              simp only [runWindow, Nat.add_sub_cancel, window_step, hs]
              exact ih clock k (by omega) (by omega)

/-- The window semantics agrees with the existing local tableau, including
early halts and their charged final instruction. -/
theorem runWindow_of_localTrace (m : Machine) (c : Config) (trace : List Config)
    (b : Bool) (clock k : Nat) (hhead : trace.head? = some c)
    (hlocal : LocalTrace m b trace) (ht : trace.length ≤ clock) (hk : clock ≤ k) :
    runWindow m clock k (.inr (window k c)) = .inl b :=
  runWindow_correct ((localTrace_iff_run m c trace.length b).mp
    ⟨trace, hhead, rfl, hlocal⟩) clock k ht hk

end Issue626.Window
