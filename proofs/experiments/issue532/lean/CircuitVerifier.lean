import proofs.experiments.issue532.lean.Idea41Core
import proofs.experiments.issue567.lean.CircuitSyntax

/-! A finite CircuitSAT verifier with universal correctness and cubic charged termination. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Issue532.CircuitVerifier
open Complexity Issue532.Idea41

def candidate : Machine := ⟨[
    [Instruction.halt false, Instruction.move 81 .zero .right, Instruction.move 0 .one .right, Instruction.halt false], -- syntax_header
    [Instruction.halt false, Instruction.move 2 .zero .right, Instruction.move 1 .one .right, Instruction.halt false], -- advance_first
    [Instruction.halt false, Instruction.move 36 .zero .right, Instruction.move 2 .one .right, Instruction.halt false], -- advance_second
    [Instruction.move 1 .one .right, Instruction.move 3 .zero .left, Instruction.move 3 .one .left, Instruction.halt false], -- append_back_gate
    [Instruction.halt false, Instruction.move 4 .zero .left, Instruction.move 4 .one .left, Instruction.move 3 .separator .left], -- append_back_sep
    [Instruction.move 4 .zero .left, Instruction.move 5 .zero .right, Instruction.move 5 .one .right, Instruction.halt false], -- append_false_end
    [Instruction.halt false, Instruction.move 6 .zero .right, Instruction.move 6 .one .right, Instruction.move 5 .separator .right], -- append_false_sep
    [Instruction.move 4 .one .left, Instruction.move 7 .zero .right, Instruction.move 7 .one .right, Instruction.halt false], -- append_true_end
    [Instruction.halt false, Instruction.move 8 .zero .right, Instruction.move 8 .one .right, Instruction.move 7 .separator .right], -- append_true_sep
    [Instruction.move 26 .blank .right, Instruction.move 9 .zero .left, Instruction.move 9 .one .left, Instruction.move 9 .separator .left], -- count_back_left
    [Instruction.halt false, Instruction.move 10 .zero .left, Instruction.move 10 .one .left, Instruction.move 9 .separator .left], -- count_back_sep
    [Instruction.move 16 .blank .left, Instruction.halt false, Instruction.halt false, Instruction.halt false], -- count_cert_empty
    [Instruction.move 15 .zero .right, Instruction.move 12 .zero .right, Instruction.move 12 .one .right, Instruction.move 15 .one .right], -- count_cert_end
    [Instruction.halt false, Instruction.move 10 .blank .left, Instruction.move 10 .separator .left, Instruction.halt false], -- count_cert_first
    [Instruction.move 18 .zero .right, Instruction.move 14 .zero .right, Instruction.move 14 .one .right, Instruction.move 18 .one .right], -- count_cert_next
    [Instruction.move 16 .blank .left, Instruction.halt false, Instruction.halt false, Instruction.halt false], -- count_check_end
    [Instruction.halt false, Instruction.move 16 .zero .left, Instruction.move 16 .one .left, Instruction.move 21 .separator .left], -- count_finish_sep
    [Instruction.halt false, Instruction.move 22 .zero .right, Instruction.move 24 .separator .right, Instruction.halt false], -- count_first
    [Instruction.halt false, Instruction.move 10 .blank .left, Instruction.move 10 .separator .left, Instruction.halt false], -- count_mark_next
    [Instruction.halt false, Instruction.move 23 .zero .right, Instruction.move 25 .separator .right, Instruction.halt false], -- count_next
    [Instruction.halt false, Instruction.move 36 .zero .right, Instruction.halt false, Instruction.move 20 .one .right], -- count_restore
    [Instruction.move 20 .blank .right, Instruction.move 21 .zero .left, Instruction.move 21 .one .left, Instruction.move 21 .separator .left], -- count_restore_left
    [Instruction.halt false, Instruction.move 22 .zero .right, Instruction.move 22 .one .right, Instruction.move 11 .separator .right], -- count_seek_empty
    [Instruction.halt false, Instruction.move 23 .zero .right, Instruction.move 23 .one .right, Instruction.move 12 .separator .right], -- count_seek_end
    [Instruction.halt false, Instruction.move 24 .zero .right, Instruction.move 24 .one .right, Instruction.move 13 .separator .right], -- count_seek_first
    [Instruction.halt false, Instruction.move 25 .zero .right, Instruction.move 25 .one .right, Instruction.move 14 .separator .right], -- count_seek_next
    [Instruction.halt false, Instruction.move 19 .zero .stay, Instruction.move 19 .one .stay, Instruction.move 26 .separator .right], -- count_skip
    [Instruction.halt false, Instruction.halt false, Instruction.halt false, Instruction.move 28 .separator .right], -- finish_boundary
    [Instruction.halt false, Instruction.move 28 .zero .right, Instruction.move 29 .one .right, Instruction.halt false], -- finish_false
    [Instruction.halt true, Instruction.move 28 .zero .right, Instruction.move 29 .one .right, Instruction.halt false], -- finish_true
    [Instruction.move 32 .blank .right, Instruction.move 30 .zero .left, Instruction.move 30 .one .left, Instruction.move 30 .separator .left], -- first_restore_false_gate
    [Instruction.halt false, Instruction.move 31 .zero .left, Instruction.move 31 .one .left, Instruction.move 30 .separator .left], -- first_restore_false_sep
    [Instruction.halt false, Instruction.move 51 .zero .right, Instruction.halt false, Instruction.move 32 .one .right], -- first_restore_false_unary
    [Instruction.move 35 .blank .right, Instruction.move 33 .zero .left, Instruction.move 33 .one .left, Instruction.move 33 .separator .left], -- first_restore_true_gate
    [Instruction.halt false, Instruction.move 34 .zero .left, Instruction.move 34 .one .left, Instruction.move 33 .separator .left], -- first_restore_true_sep
    [Instruction.halt false, Instruction.move 62 .zero .right, Instruction.halt false, Instruction.move 35 .one .right], -- first_restore_true_unary
    [Instruction.halt false, Instruction.move 27 .zero .right, Instruction.move 41 .blank .right, Instruction.halt false], -- gate
    [Instruction.move 46 .blank .right, Instruction.move 37 .zero .left, Instruction.move 37 .one .left, Instruction.move 37 .separator .left], -- lookup_first_back_gate
    [Instruction.halt false, Instruction.move 38 .zero .left, Instruction.move 38 .one .left, Instruction.move 37 .separator .left], -- lookup_first_back_sep
    [Instruction.move 43 .zero .right, Instruction.move 39 .zero .right, Instruction.move 39 .one .right, Instruction.move 43 .one .right], -- lookup_first_cursor_increment
    [Instruction.move 31 .zero .left, Instruction.move 40 .zero .right, Instruction.move 40 .one .right, Instruction.move 34 .one .left], -- lookup_first_cursor_read
    [Instruction.halt false, Instruction.move 41 .zero .right, Instruction.move 41 .one .right, Instruction.move 42 .separator .right], -- lookup_first_init
    [Instruction.halt false, Instruction.move 38 .blank .left, Instruction.move 38 .separator .left, Instruction.halt false], -- lookup_first_mark_initial
    [Instruction.halt false, Instruction.move 38 .blank .left, Instruction.move 38 .separator .left, Instruction.halt false], -- lookup_first_mark_next
    [Instruction.halt false, Instruction.move 44 .zero .right, Instruction.move 44 .one .right, Instruction.move 39 .separator .right], -- lookup_first_seek_increment
    [Instruction.halt false, Instruction.move 45 .zero .right, Instruction.move 45 .one .right, Instruction.move 40 .separator .right], -- lookup_first_seek_read
    [Instruction.halt false, Instruction.move 45 .zero .right, Instruction.move 44 .separator .right, Instruction.move 46 .separator .right], -- lookup_first_unary
    [Instruction.move 56 .blank .right, Instruction.move 47 .zero .left, Instruction.move 47 .one .left, Instruction.move 47 .separator .left], -- lookup_second_false_back_gate
    [Instruction.halt false, Instruction.move 48 .zero .left, Instruction.move 48 .one .left, Instruction.move 47 .separator .left], -- lookup_second_false_back_sep
    [Instruction.move 53 .zero .right, Instruction.move 49 .zero .right, Instruction.move 49 .one .right, Instruction.move 53 .one .right], -- lookup_second_false_cursor_increment
    [Instruction.move 74 .zero .left, Instruction.move 50 .zero .right, Instruction.move 50 .one .right, Instruction.move 74 .one .left], -- lookup_second_false_cursor_read
    [Instruction.halt false, Instruction.move 51 .zero .right, Instruction.move 51 .one .right, Instruction.move 52 .separator .right], -- lookup_second_false_init
    [Instruction.halt false, Instruction.move 48 .blank .left, Instruction.move 48 .separator .left, Instruction.halt false], -- lookup_second_false_mark_initial
    [Instruction.halt false, Instruction.move 48 .blank .left, Instruction.move 48 .separator .left, Instruction.halt false], -- lookup_second_false_mark_next
    [Instruction.halt false, Instruction.move 54 .zero .right, Instruction.move 54 .one .right, Instruction.move 49 .separator .right], -- lookup_second_false_seek_increment
    [Instruction.halt false, Instruction.move 55 .zero .right, Instruction.move 55 .one .right, Instruction.move 50 .separator .right], -- lookup_second_false_seek_read
    [Instruction.halt false, Instruction.move 57 .zero .right, Instruction.move 56 .one .right, Instruction.halt false], -- lookup_second_false_skip_first
    [Instruction.halt false, Instruction.move 55 .zero .right, Instruction.move 54 .separator .right, Instruction.move 57 .separator .right], -- lookup_second_false_unary
    [Instruction.move 67 .blank .right, Instruction.move 58 .zero .left, Instruction.move 58 .one .left, Instruction.move 58 .separator .left], -- lookup_second_true_back_gate
    [Instruction.halt false, Instruction.move 59 .zero .left, Instruction.move 59 .one .left, Instruction.move 58 .separator .left], -- lookup_second_true_back_sep
    [Instruction.move 64 .zero .right, Instruction.move 60 .zero .right, Instruction.move 60 .one .right, Instruction.move 64 .one .right], -- lookup_second_true_cursor_increment
    [Instruction.move 74 .zero .left, Instruction.move 61 .zero .right, Instruction.move 61 .one .right, Instruction.move 70 .one .left], -- lookup_second_true_cursor_read
    [Instruction.halt false, Instruction.move 62 .zero .right, Instruction.move 62 .one .right, Instruction.move 63 .separator .right], -- lookup_second_true_init
    [Instruction.halt false, Instruction.move 59 .blank .left, Instruction.move 59 .separator .left, Instruction.halt false], -- lookup_second_true_mark_initial
    [Instruction.halt false, Instruction.move 59 .blank .left, Instruction.move 59 .separator .left, Instruction.halt false], -- lookup_second_true_mark_next
    [Instruction.halt false, Instruction.move 65 .zero .right, Instruction.move 65 .one .right, Instruction.move 60 .separator .right], -- lookup_second_true_seek_increment
    [Instruction.halt false, Instruction.move 66 .zero .right, Instruction.move 66 .one .right, Instruction.move 61 .separator .right], -- lookup_second_true_seek_read
    [Instruction.halt false, Instruction.move 68 .zero .right, Instruction.move 67 .one .right, Instruction.halt false], -- lookup_second_true_skip_first
    [Instruction.halt false, Instruction.move 66 .zero .right, Instruction.move 65 .separator .right, Instruction.move 68 .separator .right], -- lookup_second_true_unary
    [Instruction.move 71 .blank .right, Instruction.move 69 .zero .left, Instruction.move 69 .one .left, Instruction.move 69 .separator .left], -- second_restore_false_gate
    [Instruction.halt false, Instruction.move 70 .zero .left, Instruction.move 70 .one .left, Instruction.move 69 .separator .left], -- second_restore_false_sep
    [Instruction.halt false, Instruction.move 72 .zero .right, Instruction.move 71 .one .right, Instruction.halt false], -- second_restore_false_skip_first
    [Instruction.halt false, Instruction.move 6 .zero .right, Instruction.halt false, Instruction.move 72 .one .right], -- second_restore_false_unary
    [Instruction.move 75 .blank .right, Instruction.move 73 .zero .left, Instruction.move 73 .one .left, Instruction.move 73 .separator .left], -- second_restore_true_gate
    [Instruction.halt false, Instruction.move 74 .zero .left, Instruction.move 74 .one .left, Instruction.move 73 .separator .left], -- second_restore_true_sep
    [Instruction.halt false, Instruction.move 76 .zero .right, Instruction.move 75 .one .right, Instruction.halt false], -- second_restore_true_skip_first
    [Instruction.halt false, Instruction.move 8 .zero .right, Instruction.halt false, Instruction.move 76 .one .right], -- second_restore_true_unary
    [Instruction.move 17 .blank .right, Instruction.move 77 .zero .left, Instruction.move 77 .one .left, Instruction.halt false], -- start_left
    [Instruction.halt false, Instruction.move 78 .zero .right, Instruction.move 78 .one .right, Instruction.halt false], -- syntax_bad
    [Instruction.halt false, Instruction.move 78 .zero .right, Instruction.move 78 .one .right, Instruction.move 77 .separator .left], -- syntax_done
    [Instruction.halt false, Instruction.move 82 .zero .right, Instruction.move 80 .one .right, Instruction.halt false], -- syntax_first
    [Instruction.halt false, Instruction.move 79 .zero .right, Instruction.move 80 .one .right, Instruction.halt false], -- syntax_marker
    [Instruction.halt false, Instruction.move 81 .zero .right, Instruction.move 82 .one .right, Instruction.halt false] -- syntax_second
]⟩

example : candidate.program.length = 83 := by decide

/-! Universal tape lemmas for the exact candidate table. State numbers are
filled from the same table as the concrete probes; no transition oracle is
introduced. The lemmas compose into the polynomial `verifier_run` proof below. -/

open Issue532.Machines

def cfg (q : Nat) (L : List Symbol) : List Symbol → Config
  | [] => ⟨q, L, .blank, []⟩
  | a :: R => ⟨q, L, a, R⟩

abbrev Rch := Reaches candidate

theorem stepR {q q' : Nat} {a w : Symbol}
    (h : candidate.instruction q a = .move q' w .right) (L R : List Symbol) :
    step candidate (cfg q L (a :: R)) = .inr (cfg q' (w :: L) R) := by
  simp only [step, cfg, h]
  cases R <;> rfl

theorem stepL {q q' : Nat} {a w l : Symbol}
    (h : candidate.instruction q a = .move q' w .left) (L R : List Symbol) :
    step candidate (cfg q (l :: L) (a :: R)) = .inr (cfg q' L (l :: w :: R)) := by
  simp only [step, cfg, h]
  rfl

theorem stepS {q q' : Nat} {a w : Symbol}
    (h : candidate.instruction q a = .move q' w .stay) (L R : List Symbol) :
    step candidate (cfg q L (a :: R)) = .inr (cfg q' L (w :: R)) := by
  simp only [step, cfg, h]
  rfl

theorem stepH {q : Nat} {a : Symbol} {b : Bool}
    (h : candidate.instruction q a = .halt b) (L R : List Symbol) :
    step candidate (cfg q L (a :: R)) = .inl b := by
  simp only [step, cfg, h]

theorem trans {c d e : Config} {t u : Nat}
    (h : Rch c t d) (h' : Rch d u e) : Rch c (t + u) e := by
  induction h with
  | refl => simpa using h'
  | next hs _ ih => rw [Nat.add_right_comm]; exact Reaches.next hs (ih h')

theorem R1 {q q' : Nat} {a w : Symbol} {L R : List Symbol} {t : Nat} {E : Config}
    (h : candidate.instruction q a = .move q' w .right)
    (hr : Rch (cfg q' (w :: L) R) t E) :
    Rch (cfg q L (a :: R)) (t + 1) E := Reaches.next (stepR h L R) hr

theorem L1 {q q' : Nat} {a w l : Symbol} {L R : List Symbol} {t : Nat} {E : Config}
    (h : candidate.instruction q a = .move q' w .left)
    (hr : Rch (cfg q' L (l :: w :: R)) t E) :
    Rch (cfg q (l :: L) (a :: R)) (t + 1) E := Reaches.next (stepL h L R) hr

theorem walkR (q : Nat) : ∀ (w L R : List Symbol),
    (∀ a ∈ w, candidate.instruction q a = .move q a .right) →
    Rch (cfg q L (w ++ R)) w.length (cfg q (w.reverse ++ L) R)
  | [], L, R, _ => Reaches.refl _
  | a :: w, L, R, h => by
      have ih := walkR q w (a :: L) R
        (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
      have hr := R1 (L := L) (R := w ++ R) (h a (List.mem_cons_self ..)) ih
      simpa [Nat.add_comm] using hr

/-- A left scan stops on the explicit marker, preserving every scanned cell.
The marker is not scanned by this lemma. -/
theorem walkL (q : Nat) (marker : Symbol) (L : List Symbol) :
    ∀ (w : List Symbol) (a : Symbol) (R : List Symbol),
    (∀ b ∈ a :: w, candidate.instruction q b = .move q b .left) →
    Rch (cfg q (w ++ marker :: L) (a :: R)) (w.length + 1)
      (cfg q L (marker :: w.reverse ++ a :: R))
  | [], a, R, h => L1 (h a (List.mem_cons_self ..)) (Reaches.refl _)
  | b :: w, a, R, h => by
      have ih := walkL q marker L w b (a :: R)
        (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      have hr := L1 (L := w ++ marker :: L) (h a (List.mem_cons_self ..)) ih
      simpa [Nat.add_comm, Nat.add_left_comm] using hr

/-- Turn at a boundary, then scan left until the distinguished marker. -/
theorem rewind (q q' : Nat) (marker a : Symbol) (w L R : List Symbol)
    (ha : candidate.instruction q a = .move q' a .left)
    (hw : ∀ b ∈ w, candidate.instruction q' b = .move q' b .left) :
    Rch (cfg q (w ++ marker :: L) (a :: R)) (w.length + 1)
      (cfg q' L (marker :: w.reverse ++ a :: R)) := by
  cases w with
  | nil => exact L1 ha (Reaches.refl _)
  | cons b w =>
      have hr := walkL q' marker L w b (a :: R) hw
      simpa [Nat.add_comm] using L1 ha hr

theorem bit_mem {a : Symbol} {w : Word} (h : a ∈ w.map Symbol.ofBool) :
    a = .zero ∨ a = .one := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
  cases b <;> simp [Symbol.ofBool]

def cursor : Bool → Symbol
  | false => .blank
  | true => .separator

/-- For every suffix and every nonempty wire list, the first lookup's initial
shuttle finds the circuit/certificate boundary, marks exactly the first wire,
and returns to the active gate. The circuit suffix and wire bits are preserved.
The equation gives an exact number of charged, nonhalting instructions. -/
theorem lookup_first_initial (w : Word) (b : Bool) (v : Word) (L : List Symbol) :
    Rch (cfg 41 (.blank :: L)
      (w.map Symbol.ofBool ++ .separator :: (b :: v).map Symbol.ofBool))
      (2 * w.length + 4)
      (cfg 46 (.blank :: L)
        (w.map Symbol.ofBool ++ .separator :: cursor b :: v.map Symbol.ofBool)) := by
  have h1 := walkR 41 (w.map Symbol.ofBool) (.blank :: L)
    (.separator :: (b :: v).map Symbol.ofBool) (by
      intro a ha
      rcases bit_mem ha with rfl | rfl <;> rfl)
  have h4 := rewind 38 37
    .blank .separator (w.map Symbol.ofBool).reverse L (cursor b :: v.map Symbol.ofBool)
    rfl (by
      intro a ha
      rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> rfl)
  have h5 : Rch (cfg 37 L
      (.blank :: w.map Symbol.ofBool ++ .separator :: cursor b :: v.map Symbol.ofBool))
      1 (cfg 46 (.blank :: L)
        (w.map Symbol.ofBool ++ .separator :: cursor b :: v.map Symbol.ofBool)) :=
    R1 rfl (Reaches.refl _)
  simp only [List.reverse_reverse, List.length_reverse, List.length_map] at h4
  have h45 := trans h4 h5
  have h345 := L1 (q := 42) (a := Symbol.ofBool b)
    (w := cursor b) (by cases b <;> rfl) h45
  have h2345 := R1 (q := 41) (a := .separator) rfl h345
  have h := trans h1 h2345
  have he : (w.map Symbol.ofBool).length + (w.length + 1 + 1 + 1 + 1) =
      2 * w.length + 4 := by simp only [List.length_map]; omega
  rw [he] at h
  exact h


open Issue567.CircuitSyntax (Phase)

def syntaxIdx : Phase → Nat
  | .header => 0
  | .marker => 81
  | .firstWire => 80
  | .secondWire => 82
  | .done => 79
  | .bad => 78

def phaseAfter : Phase → Word → Phase
  | q, [] => q
  | q, b :: w => phaseAfter (Issue567.CircuitSyntax.next q b) w

theorem phaseAfter_spec (q : Phase) (w : Word) :
    Issue567.CircuitSyntax.syntaxFrom q w = (phaseAfter q w == .done) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih => exact ih _

/-- The candidate's parser consumes exactly the circuit word, stopping on the
input/certificate separator without touching a certificate bit. -/
theorem syntax_scan_reaches (q : Phase) (w : Word) (L R : List Symbol) :
    Rch (cfg (syntaxIdx q) L (w.map Symbol.ofBool ++ .separator :: R)) w.length
      (cfg (syntaxIdx (phaseAfter q w)) ((w.map Symbol.ofBool).reverse ++ L)
        (.separator :: R)) := by
  induction w generalizing q L with
  | nil => exact Reaches.refl _
  | cons b w ih =>
      have hs : candidate.instruction (syntaxIdx q) (Symbol.ofBool b) =
          .move (syntaxIdx (Issue567.CircuitSyntax.next q b)) (Symbol.ofBool b) .right := by
        cases q <;> cases b <;> rfl
      have hr := R1 hs (ih (Issue567.CircuitSyntax.next q b) (Symbol.ofBool b :: L))
      simpa [phaseAfter, Nat.add_comm] using hr

theorem paired_eq (w cert : Word) : pairedInput w cert =
    cfg (syntaxIdx .header) [] (w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool) := by
  unfold pairedInput
  simp only [List.append_assoc, List.singleton_append]
  cases w <;> rfl

/-- Every malformed circuit word is rejected by the actual 83-state table,
for every certificate, in exactly |w| + 1 charged instructions. -/
theorem malformed_reject (w cert : Word)
    (hbad : Issue567.CircuitSyntax.circuitSyntax w = false) :
    Run candidate (pairedInput w cert) (w.length + 1) false := by
  have hscan := syntax_scan_reaches .header w [] (cert.map Symbol.ofBool)
  have hs : candidate.instruction (syntaxIdx (phaseAfter .header w)) .separator =
      .halt false := by
    have hf : (phaseAfter .header w == .done) = false := by
      rw [← phaseAfter_spec]
      exact hbad
    cases hp : phaseAfter .header w <;> simp only [hp] at hf <;> try rfl
    contradiction
  rw [paired_eq]
  exact hscan.run (Run.halt (stepH hs _ _))

/-- Left scans at the initial tape boundary create the explicit blank cell
required by the subsequent certificate matching phase. -/
theorem walkLEnd (q : Nat) : ∀ (w : List Symbol) (a : Symbol) (R : List Symbol),
    (∀ b ∈ a :: w, candidate.instruction q b = .move q b .left) →
    Rch (cfg q w (a :: R)) (w.length + 1)
      (cfg q [] (.blank :: w.reverse ++ a :: R))
  | [], a, R, h => by
      apply Reaches.next (c' := cfg q [] (.blank :: a :: R))
      · simp only [step, cfg, h a (List.mem_cons_self ..)]
        rfl
      · exact Reaches.refl _
  | b :: w, a, R, h => by
      have ih := walkLEnd q w b (a :: R)
        (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      simpa [Nat.add_comm, Nat.add_left_comm] using L1 (h a (List.mem_cons_self ..)) ih

theorem rewindEnd (q q' : Nat) (a : Symbol) (w R : List Symbol)
    (ha : candidate.instruction q a = .move q' a .left)
    (hw : ∀ b ∈ w, candidate.instruction q' b = .move q' b .left) :
    Rch (cfg q w (a :: R)) (w.length + 1)
      (cfg q' [] (.blank :: w.reverse ++ a :: R)) := by
  cases w with
  | nil =>
      apply Reaches.next (c' := cfg q' [] (.blank :: a :: R))
      · simp only [step, cfg, ha]; rfl
      · exact Reaches.refl _
  | cons b w => simpa [Nat.add_comm] using L1 ha (walkLEnd q' w b (a :: R) hw)

/-- For every well-formed encoding and certificate, the actual parser and
rewind enter the length-matching phase with the entire input preserved. -/
theorem valid_start (w cert : Word)
    (hvalid : Issue567.CircuitSyntax.circuitSyntax w = true) :
    Rch (pairedInput w cert) (2 * w.length + 2)
      (cfg 17 [.blank]
        (w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool)) := by
  have hf : phaseAfter .header w = .done := by
    have he : (phaseAfter .header w == .done) = true := by
      rw [← phaseAfter_spec]; exact hvalid
    exact beq_iff_eq.mp he
  have h1 := syntax_scan_reaches .header w [] (cert.map Symbol.ofBool)
  rw [hf, List.append_nil] at h1
  have h2 := rewindEnd (syntaxIdx .done) 77 .separator
    (w.map Symbol.ofBool).reverse (cert.map Symbol.ofBool) rfl (by
      intro a ha
      rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> rfl)
  simp only [List.reverse_reverse, List.length_reverse, List.length_map] at h2
  have h3 : Rch (cfg 77 []
      (.blank :: w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool))
      1 (cfg 17 [.blank]
        (w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool)) :=
    R1 rfl (Reaches.refl _)
  have h := trans h1 (trans h2 h3)
  rw [← paired_eq] at h
  have ht : w.length + (w.length + 1 + 1) = 2 * w.length + 2 := by omega
  rw [ht] at h
  exact h

def lastFrom : Bool → Word → Bool
  | b, [] => b
  | _, b :: w => lastFrom b w

/-- The final output pass charges every visited wire and the halt instruction. -/
theorem finish_run (b : Bool) (w : Word) (L : List Symbol) :
    Run candidate (cfg (if b then 29 else 28) L
      (w.map Symbol.ofBool)) (w.length + 1) (lastFrom b w) := by
  induction w generalizing b L with
  | nil =>
      apply Run.halt
      cases b <;> rfl
  | cons a w ih =>
      have hs : candidate.instruction (if b then 29 else 28)
          (Symbol.ofBool a) =
          .move (if a then 29 else 28) (Symbol.ofBool a) .right := by
        cases b <;> cases a <;> rfl
      exact Run.next (stepR hs _ _) (ih a (Symbol.ofBool a :: L))

theorem lastFrom_eq_getLastD (b : Bool) (w : Word) : lastFrom b w = w.getLastD b := by
  induction w generalizing b with
  | nil => rfl
  | cons a w ih =>
      cases w with
      | nil => rfl
      | cons a' w => exact ih a

/-- An empty gate suffix returns precisely the last wire, defaulting to false
on an empty wire list. This proves the terminal gate-loop case for all wires. -/
theorem gate_empty_run (w : Word) (L : List Symbol) :
    Run candidate (cfg 36 L (.zero :: .separator :: w.map Symbol.ofBool))
      (w.length + 3) (w.getLastD false) := by
  have h1 : Rch (cfg 36 L (.zero :: .separator :: w.map Symbol.ofBool))
      2 (cfg 28 (.separator :: .zero :: L) (w.map Symbol.ofBool)) :=
    R1 rfl (R1 rfl (Reaches.refl _))
  have h := h1.run (finish_run false w (.separator :: .zero :: L))
  rw [lastFrom_eq_getLastD] at h
  simpa [Nat.add_comm, Nat.add_left_comm] using h



/-! Certificate-matching shuttles, with exact charged costs. -/

def ones (n : Nat) : List Symbol := List.replicate n .one
def marks (n : Nat) : List Symbol := List.replicate n .separator

theorem cfg_blank (q : Nat) (L : List Symbol) : cfg q L [.blank] = cfg q L [] := rfl

theorem marks_mem {a : Symbol} {n : Nat} (h : a ∈ marks n) : a = .separator := by
  exact (List.mem_replicate.mp h).2

theorem ones_mem {a : Symbol} {n : Nat} (h : a ∈ ones n) : a = .one := by
  exact (List.mem_replicate.mp h).2

/-- Return from a newly marked certificate bit to the next header tick.
The cursor encodes its original Boolean value and all earlier bits are restored. -/
theorem count_return (p : Nat) (r u : Word) (b : Bool) (R : List Symbol) (hne : r ≠ []) :
    Rch (cfg 10
      ((u.map Symbol.ofBool).reverse ++ .separator ::
        (r.map Symbol.ofBool).reverse ++ marks p ++ [.blank])
      (Symbol.ofBool b :: R))
      (u.length + r.length + 2 * p + 4)
      (cfg 19 (marks p ++ [.blank])
        (r.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R)) := by
  have h1 := walkL 10 .separator
    ((r.map Symbol.ofBool).reverse ++ marks p ++ [.blank])
    (u.map Symbol.ofBool).reverse (Symbol.ofBool b) R (by
      intro a ha
      rcases List.mem_cons.mp ha with h | h
      · subst a; cases b <;> rfl
      · rcases bit_mem (List.mem_reverse.mp h) with rfl | rfl <;> rfl)
  have h2 := rewind 10 9 .blank .separator
    ((r.map Symbol.ofBool).reverse ++ marks p) []
    ((u ++ [b]).map Symbol.ofBool ++ R) rfl (by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · rcases bit_mem (List.mem_reverse.mp h) with rfl | rfl <;> rfl
      · have := marks_mem h; subst a; rfl)
  have h3 := walkR 26 (marks p) [.blank]
    (r.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R) (by
      intro a ha; have := marks_mem ha; subst a; rfl)
  -- The remaining header always has a bit; an empty remainder is not a
  -- well-formed count state, so the generic shuttle ends before the stay.
  have h4 : Rch (cfg 26 (marks p ++ [.blank])
      (r.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R)) 1
      (cfg 19 (marks p ++ [.blank])
        (r.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R)) := by
    cases r with
    | nil => exact False.elim (hne rfl)
    | cons a r =>
        apply Reaches.next (c' := cfg 19 (marks p ++ [.blank])
          ((a :: r).map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R))
        · exact stepS (by cases a <;> rfl) _ _
        · exact Reaches.refl _
  simp only [marks, List.reverse_reverse, List.length_reverse, List.length_map,
    List.length_append, List.length_replicate, List.reverse_append,
    List.reverse_replicate, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append, List.cons_append] at h1 h2 h3 h4 ⊢
  have h3' := trans h3 h4
  have h23 := R1 (q := 9) (a := .blank) rfl h3'
  have h23' := trans h2 h23
  have h := trans h1 h23'
  simpa only [Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.two_mul] using h

theorem restore_marks (p : Nat) (L R : List Symbol) :
    Rch (cfg 20 L (marks p ++ R)) p
      (cfg 20 (ones p ++ L) R) := by
  induction p generalizing L with
  | zero => exact Reaches.refl _
  | succ p ih =>
      have h := R1 (q := 20) (a := .separator) (w := .one) rfl
        (ih (.one :: L))
      have he : ones (p + 1) ++ L = ones p ++ .one :: L := by
        simp only [ones, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [he]
      simpa only [marks, List.replicate_succ, List.cons_append] using h

/-- The successful length check restores the unary header and keeps the
certificate unchanged. The final explicit blank was created by moving left
from the first blank after the certificate. -/
theorem count_finish (q p : Nat) (r cert : Word)
    (hq : candidate.instruction q .blank = .move 16 .blank .left) :
    Rch (cfg q ((cert.map Symbol.ofBool).reverse ++ .separator ::
        (r.map Symbol.ofBool).reverse ++ .zero :: marks p ++ [.blank]) [])
      (cert.length + r.length + 2 * p + 5)
      (cfg 36 (.zero :: ones p ++ [.blank])
        (r.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool ++ [.blank])) := by
  have h1 := rewind q 16 .separator .blank
    (cert.map Symbol.ofBool).reverse
    ((r.map Symbol.ofBool).reverse ++ .zero :: marks p ++ [.blank]) [] hq (by
      intro a ha; rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> rfl)
  have h2 := rewind 16 21 .blank .separator
    ((r.map Symbol.ofBool).reverse ++ .zero :: marks p) []
    (cert.map Symbol.ofBool ++ [.blank]) rfl (by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · rcases bit_mem (List.mem_reverse.mp h) with rfl | rfl <;> rfl
      · rcases List.mem_cons.mp h with h | h
        · subst a; rfl
        · have := marks_mem h; subst a; rfl)
  have h3 := restore_marks p [.blank]
    (.zero :: r.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool ++ [.blank])
  have h4 : Rch (cfg 20 (ones p ++ [.blank])
      (.zero :: r.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool ++ [.blank])) 1
      (cfg 36 (.zero :: ones p ++ [.blank])
        (r.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool ++ [.blank])) :=
    R1 rfl (Reaches.refl _)
  simp only [marks, List.reverse_reverse, List.length_reverse, List.length_map,
    List.length_append, List.length_cons, List.length_replicate, List.reverse_append,
    List.reverse_replicate, List.reverse_cons, List.reverse_nil,
    List.append_assoc, List.singleton_append, List.cons_append, List.append_nil, List.nil_append] at h1 h2 h3 h4 ⊢
  have h34 := trans h3 h4
  have h234 := trans h2 (R1 (q := 21) (a := .blank) rfl h34)
  have h := trans h1 h234
  rw [cfg_blank] at h
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.two_mul] using h

theorem count_advance (p n : Nat) (w u : Word) (b c : Bool) (v : Word) :
    Rch (cfg 19 (marks p ++ [.blank])
      (ones (n + 1) ++ .zero :: w.map Symbol.ofBool ++ .separator ::
        u.map Symbol.ofBool ++ cursor b :: (c :: v).map Symbol.ofBool))
      (2 * (n + w.length + u.length + p) + 12)
      (cfg 19 (marks (p + 1) ++ [.blank])
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator ::
          (u ++ [b]).map Symbol.ofBool ++ cursor c :: v.map Symbol.ofBool)) := by
  let r : Word := List.replicate n true ++ false :: w
  have hr : r.map Symbol.ofBool = ones n ++ .zero :: w.map Symbol.ofBool := by
    simp [r, ones, Symbol.ofBool]
  have h1 := walkR 25 (r.map Symbol.ofBool)
    (marks (p + 1) ++ [.blank])
    (.separator :: u.map Symbol.ofBool ++ cursor b :: (c :: v).map Symbol.ofBool) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 := walkR 14 (u.map Symbol.ofBool)
    (.separator :: (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++ [.blank])
    (cursor b :: (c :: v).map Symbol.ofBool) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h3 := count_return (p + 1) r u b (cursor c :: v.map Symbol.ofBool) (by
    simp [r])
  have h4 := L1 (q := 18) (a := Symbol.ofBool c)
    (w := cursor c) (l := Symbol.ofBool b) (by cases c <;> rfl) h3
  have h5 := R1 (q := 14) (a := cursor b)
    (w := Symbol.ofBool b) (by cases b <;> rfl) h4
  simp only [List.length_map, List.map_cons, List.append_assoc, List.cons_append] at h1 h2 h5
  have h6 := trans h2 h5
  have h7 := R1 (q := 25) (a := .separator) rfl h6
  have h8 := trans h1 h7
  have h9 := R1 (q := 19) (a := .one) (w := .separator) rfl h8
  have hp : .separator :: marks p = marks (p + 1) := by
    simp [marks, List.replicate_succ]
  have hn : .one :: ones n = ones (n + 1) := by
    simp [ones, List.replicate_succ]
  simp only [← hp, ← hn, List.cons_append, hr, List.append_assoc] at h9 ⊢
  have ht : r.length + (u.length + (u.length + r.length + 2 * (p + 1) + 4 + 1 + 1) + 1) + 1 =
      2 * (n + w.length + u.length + p) + 12 := by
    simp only [r, List.length_append, List.length_replicate, List.length_cons]
    omega
  rw [ht] at h9
  exact h9

theorem count_short (p n : Nat) (w u : Word) (b : Bool) :
    Run candidate (cfg 19 (marks p ++ [.blank])
      (ones (n + 1) ++ .zero :: w.map Symbol.ofBool ++ .separator ::
        u.map Symbol.ofBool ++ [cursor b]))
      (n + w.length + u.length + 5) false := by
  let r : Word := List.replicate n true ++ false :: w
  have hr : r.map Symbol.ofBool = ones n ++ .zero :: w.map Symbol.ofBool := by
    simp [r, ones, Symbol.ofBool]
  have h1 := walkR 25 (r.map Symbol.ofBool)
    (marks (p + 1) ++ [.blank]) (.separator :: u.map Symbol.ofBool ++ [cursor b]) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 := walkR 14 (u.map Symbol.ofBool)
    (.separator :: (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++ [.blank]) [cursor b] (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h3 : Run candidate (cfg 18
      (Symbol.ofBool b :: (u.map Symbol.ofBool).reverse ++
        .separator :: (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++ [.blank]) []) 1 false :=
    Run.halt (by rfl)
  have h4 := Run.next (stepR (q := 14) (a := cursor b)
    (w := Symbol.ofBool b) (by cases b <;> rfl) _ _) h3
  change Run candidate (cfg 14
    ((u.map Symbol.ofBool).reverse ++ .separator :: (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++ [.blank])
    [cursor b]) (1 + 1) false at h4
  simp only [List.append_eq, List.append_assoc, List.cons_append] at h2 h4
  have h5 := h2.run h4
  have h6 := Run.next (stepR (q := 25) (a := .separator) rfl _ _) h5
  have h7 := h1.run h6
  have h8 := Run.next (stepR (q := 19) (a := .one) (w := .separator) rfl _ _) h7
  simpa only [hr, ones, marks, List.replicate_succ, List.append_eq, List.length_map,
    List.length_append, List.length_cons, List.length_replicate, List.cons_append,
    List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h8

theorem count_end_success (p : Nat) (w u : Word) (b : Bool) :
    Rch (cfg 19 (marks p ++ [.blank])
      (.zero :: w.map Symbol.ofBool ++ .separator :: u.map Symbol.ofBool ++ [cursor b]))
      (2 * (w.length + u.length + p) + 9)
      (cfg 36 (.zero :: ones p ++ [.blank])
        (w.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ [.blank])) := by
  have h1 := walkR 23 (w.map Symbol.ofBool)
    (.zero :: marks p ++ [.blank]) (.separator :: u.map Symbol.ofBool ++ [cursor b]) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 := walkR 12 (u.map Symbol.ofBool)
    (.separator :: (w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ [.blank]) [cursor b] (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h3 := count_finish 15 p w (u ++ [b]) rfl
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  have h4 := R1 (q := 12) (a := cursor b)
    (w := Symbol.ofBool b) (by cases b <;> rfl) h3
  have h5 := trans h2 h4
  have h6 := R1 (q := 23) (a := .separator) rfl h5
  have h7 := trans h1 h6
  have h8 := R1 (q := 19) (a := .zero) rfl h7
  have ht : (w.map Symbol.ofBool).length +
      ((u.map Symbol.ofBool).length + ((u ++ [b]).length + w.length + 2 * p + 5 + 1) + 1) + 1 =
      2 * (w.length + u.length + p) + 9 := by
    simp only [List.length_map, List.length_append, List.length_cons, List.length_nil]; omega
  rw [ht] at h8
  exact h8

theorem count_end_long (p : Nat) (w u : Word) (b c : Bool) (v : Word) :
    Run candidate (cfg 19 (marks p ++ [.blank])
      (.zero :: w.map Symbol.ofBool ++ .separator :: u.map Symbol.ofBool ++
        cursor b :: (c :: v).map Symbol.ofBool))
      (w.length + u.length + 4) false := by
  have h1 := walkR 23 (w.map Symbol.ofBool)
    (.zero :: marks p ++ [.blank])
    (.separator :: u.map Symbol.ofBool ++ cursor b :: (c :: v).map Symbol.ofBool) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 := walkR 12 (u.map Symbol.ofBool)
    (.separator :: (w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ [.blank])
    (cursor b :: (c :: v).map Symbol.ofBool) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h3 : Run candidate (cfg 15
      (Symbol.ofBool b :: (u.map Symbol.ofBool).reverse ++ .separator ::
        (w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ [.blank])
      ((c :: v).map Symbol.ofBool)) 1 false := Run.halt (by cases c <;> rfl)
  have h4 := Run.next (stepR (q := 12) (a := cursor b)
    (w := Symbol.ofBool b) (by cases b <;> rfl) _ _) h3
  change Run candidate (cfg 12
    ((u.map Symbol.ofBool).reverse ++ .separator :: (w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ [.blank])
    (cursor b :: (c :: v).map Symbol.ofBool)) (1 + 1) false at h4
  simp only [List.append_eq, List.append_assoc, List.cons_append] at h2 h4
  have h5 := h2.run h4
  have h6 := Run.next (stepR (q := 23) (a := .separator) rfl _ _) h5
  have h7 := h1.run h6
  have h8 := Run.next (stepR (q := 19) (a := .zero) rfl _ _) h7
  simpa only [List.append_eq, List.map_cons, List.cons_append, List.append_assoc,
    List.length_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h8

theorem count_tail_success (n : Nat) : ∀ (p K : Nat) (w u : Word) (b : Bool) (v : Word),
    v.length = n → p + n + w.length + u.length + v.length + 4 ≤ K →
    ∃ t, t ≤ 32 * (n + 1) * K ∧
      Rch (cfg 19 (marks p ++ [.blank])
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator ::
          u.map Symbol.ofBool ++ cursor b :: v.map Symbol.ofBool)) t
        (cfg 36 (.zero :: ones (p + n) ++ [.blank])
          (w.map Symbol.ofBool ++ .separator :: (u ++ b :: v).map Symbol.ofBool ++ [.blank])) := by
  induction n with
  | zero =>
      intro p K w u b v hv hK
      have hv' : v = [] := List.eq_nil_of_length_eq_zero hv
      subst v
      exact ⟨2 * (w.length + u.length + p) + 9, by simp only [List.length_nil] at hK; omega,
        by simpa only [ones, List.replicate_zero, List.nil_append, List.map_nil,
          List.append_nil, Nat.add_zero] using count_end_success p w u b⟩
  | succ n ih =>
      intro p K w u b v hv hK
      cases v with
      | nil => simp at hv
      | cons c v =>
          obtain ⟨t, ht, hrun⟩ := ih (p + 1) K w (u ++ [b]) c v
            (by simpa only [List.length_cons] using Nat.succ.inj hv)
            (by simp only [List.length_cons, List.length_append, List.length_nil] at hK ⊢; omega)
          have hstep := count_advance p n w u b c v
          have hs : 2 * (n + w.length + u.length + p) + 12 ≤ 32 * K := by
            simp only [List.length_cons] at hK; omega
          refine ⟨2 * (n + w.length + u.length + p) + 12 + t, ?_, ?_⟩
          · change _ ≤ 32 * (n + 2) * K
            calc
              _ ≤ 32 * K + 32 * (n + 1) * K := Nat.add_le_add hs ht
              _ = 32 * (n + 1 + 1) * K := by simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
          · have h := trans hstep hrun
            simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.map_cons, List.map_append, List.map_nil, List.append_assoc,
              List.singleton_append, List.cons_append, List.nil_append] using h

theorem count_tail_reject (n : Nat) : ∀ (p K : Nat) (w u : Word) (b : Bool) (v : Word),
    v.length ≠ n → p + n + w.length + u.length + v.length + 4 ≤ K →
    ∃ t, t ≤ 32 * (n + 1) * K ∧
      Run candidate (cfg 19 (marks p ++ [.blank])
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator ::
          u.map Symbol.ofBool ++ cursor b :: v.map Symbol.ofBool)) t false := by
  induction n with
  | zero =>
      intro p K w u b v hv hK
      cases v with
      | nil => exact False.elim (hv rfl)
      | cons c v =>
          refine ⟨w.length + u.length + 4, by simp only [List.length_cons] at hK; omega, ?_⟩
          simpa only [ones, List.replicate_zero, List.nil_append] using count_end_long p w u b c v
  | succ n ih =>
      intro p K w u b v hv hK
      cases v with
      | nil =>
          have hs : n + w.length + u.length + 5 ≤ 32 * K := by
            simp only [List.length_nil] at hK; omega
          have hm : 32 * K ≤ 32 * (n + 1 + 1) * K :=
            Nat.mul_le_mul_right K (by omega)
          exact ⟨n + w.length + u.length + 5, Nat.le_trans hs hm,
            by simpa only [List.map_nil] using count_short p n w u b⟩
      | cons c v =>
          obtain ⟨t, ht, hrun⟩ := ih (p + 1) K w (u ++ [b]) c v
            (by simp only [List.length_cons] at hv; omega)
            (by simp only [List.length_cons, List.length_append, List.length_nil] at hK ⊢; omega)
          have hstep := count_advance p n w u b c v
          have hs : 2 * (n + w.length + u.length + p) + 12 ≤ 32 * K := by
            simp only [List.length_cons] at hK; omega
          refine ⟨2 * (n + w.length + u.length + p) + 12 + t, ?_, hstep.run hrun⟩
          calc
            _ ≤ 32 * K + 32 * (n + 1) * K := Nat.add_le_add hs ht
            _ = 32 * (n + 1 + 1) * K := by simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega

theorem count_return_sep (p : Nat) (r : Word) (R : List Symbol) (hne : r ≠ []) :
    Rch (cfg 10
      ((r.map Symbol.ofBool).reverse ++ marks p ++ [.blank]) (.separator :: R))
      (r.length + 2 * p + 3)
      (cfg 19 (marks p ++ [.blank]) (r.map Symbol.ofBool ++ .separator :: R)) := by
  have h1 := rewind 10 9 .blank .separator
    ((r.map Symbol.ofBool).reverse ++ marks p) [] R rfl (by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · rcases bit_mem (List.mem_reverse.mp h) with rfl | rfl <;> rfl
      · have := marks_mem h; subst a; rfl)
  have h2 := walkR 26 (marks p) [.blank] (r.map Symbol.ofBool ++ .separator :: R) (by
    intro a ha; have := marks_mem ha; subst a; rfl)
  have h3 : Rch (cfg 26 (marks p ++ [.blank])
      (r.map Symbol.ofBool ++ .separator :: R)) 1
      (cfg 19 (marks p ++ [.blank]) (r.map Symbol.ofBool ++ .separator :: R)) := by
    cases r with
    | nil => exact False.elim (hne rfl)
    | cons a r =>
        exact Reaches.next (stepS (by cases a <;> rfl) _ _) (Reaches.refl _)
  simp only [marks, List.reverse_append, List.reverse_replicate, List.reverse_reverse,
    List.length_append, List.length_reverse, List.length_map, List.length_replicate,
    List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  have h := trans h1 (R1 (q := 9) (a := .blank) rfl (trans h2 h3))
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem count_first_start (n : Nat) (w : Word) (b : Bool) (v : Word) :
    Rch (cfg 17 [.blank]
      (ones (n + 1) ++ .zero :: w.map Symbol.ofBool ++ .separator :: (b :: v).map Symbol.ofBool))
      (2 * (n + w.length) + 10)
      (cfg 19 (marks 1 ++ [.blank])
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator :: cursor b :: v.map Symbol.ofBool)) := by
  let r : Word := List.replicate n true ++ false :: w
  have hr : r.map Symbol.ofBool = ones n ++ .zero :: w.map Symbol.ofBool := by
    simp [r, ones, Symbol.ofBool]
  have h1 := walkR 24 (r.map Symbol.ofBool) [.separator, .blank]
    (.separator :: (b :: v).map Symbol.ofBool) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 := count_return_sep 1 r (cursor b :: v.map Symbol.ofBool) (by simp [r])
  have h3 := L1 (q := 13) (a := Symbol.ofBool b)
    (w := cursor b) (l := .separator) (by cases b <;> rfl) h2
  have h4 := R1 (q := 24) (a := .separator) rfl h3
  simp only [marks, List.replicate_succ, List.replicate_zero, List.cons_append,
    List.nil_append, List.map_cons, List.append_assoc] at h1 h4
  have h5 := trans h1 h4
  have h6 := R1 (q := 17) (a := .one) (w := .separator) rfl h5
  simpa only [hr, ones, marks, List.replicate_succ, List.replicate_zero, List.append_eq,
    r, List.map_cons, List.length_map, List.length_append, List.length_replicate, List.length_cons,
    List.cons_append, List.nil_append, List.append_assoc,
    Nat.mul_add, Nat.mul_one, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h6

theorem count_first_short (n : Nat) (w : Word) :
    Run candidate (cfg 17 [.blank]
      (ones (n + 1) ++ .zero :: w.map Symbol.ofBool ++ [.separator]))
      (n + w.length + 4) false := by
  let r : Word := List.replicate n true ++ false :: w
  have hr : r.map Symbol.ofBool = ones n ++ .zero :: w.map Symbol.ofBool := by
    simp [r, ones, Symbol.ofBool]
  have h1 := walkR 24 (r.map Symbol.ofBool) [.separator, .blank]
    [.separator] (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 : Run candidate (cfg 13
      (.separator :: (r.map Symbol.ofBool).reverse ++ [.separator, .blank]) []) 1 false :=
    Run.halt (by rfl)
  have h3 := Run.next (stepR (q := 24) (a := .separator) rfl _ _) h2
  have h4 := h1.run h3
  have h5 := Run.next (stepR (q := 17) (a := .one) (w := .separator) rfl _ _) h4
  simpa only [hr, ones, List.replicate_succ, List.append_eq, r,
    List.length_map, List.length_append, List.length_replicate, List.length_cons,
    List.cons_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h5

theorem count_zero_success (w : Word) :
    Rch (cfg 17 [.blank]
      (.zero :: w.map Symbol.ofBool ++ [.separator]))
      (2 * w.length + 7)
      (cfg 36 [.zero, .blank] (w.map Symbol.ofBool ++ [.separator, .blank])) := by
  have h1 := walkR 22 (w.map Symbol.ofBool) [.zero, .blank]
    [.separator] (by intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 := count_finish 11 0 w [] rfl
  simp only [List.map_nil, List.reverse_nil, List.nil_append, List.append_nil, ones,
    marks, List.replicate_zero, Nat.zero_mul, Nat.zero_add, List.cons_append,
    List.append_assoc, List.singleton_append, List.length_nil] at h2
  have h3 := R1 (q := 22) (a := .separator) rfl h2
  have h4 := trans h1 h3
  have h5 := R1 (q := 17) (a := .zero) rfl h4
  simpa only [List.cons_append, List.length_map, Nat.zero_add, Nat.add_zero,
    Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h5

theorem count_zero_long (w : Word) (b : Bool) (v : Word) :
    Run candidate (cfg 17 [.blank]
      (.zero :: w.map Symbol.ofBool ++ .separator :: (b :: v).map Symbol.ofBool))
      (w.length + 3) false := by
  have h1 := walkR 22 (w.map Symbol.ofBool) [.zero, .blank]
    (.separator :: (b :: v).map Symbol.ofBool) (by
      intro a ha; rcases bit_mem ha with rfl | rfl <;> rfl)
  have h2 : Run candidate (cfg 11
      (.separator :: (w.map Symbol.ofBool).reverse ++ [.zero, .blank])
      ((b :: v).map Symbol.ofBool)) 1 false := Run.halt (by cases b <;> rfl)
  have h3 := Run.next (stepR (q := 22) (a := .separator) rfl _ _) h2
  have h4 := h1.run h3
  have h5 := Run.next (stepR (q := 17) (a := .zero) rfl _ _) h4
  simpa only [List.append_eq, List.cons_append, List.append_assoc, List.length_map,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h5

/-- Every exact-length certificate reaches gate evaluation, with all bits
preserved, within a quadratic number of real table instructions. -/
theorem count_success (n : Nat) (w cert : Word) (hc : cert.length = n) :
    ∃ t, t ≤ 64 * (n + 1) * (n + w.length + cert.length + 4) ∧
      Rch (cfg 17 [.blank]
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool)) t
        (cfg 36 (.zero :: ones n ++ [.blank])
          (w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool ++ [.blank])) := by
  cases n with
  | zero =>
      have hc' : cert = [] := List.eq_nil_of_length_eq_zero hc
      subst cert
      exact ⟨2 * w.length + 7, by simp only [List.length_nil]; omega,
        by simpa only [ones, List.replicate_zero, List.nil_append, List.map_nil,
          List.append_assoc, List.singleton_append] using count_zero_success w⟩
  | succ n =>
      cases cert with
      | nil => simp at hc
      | cons b v =>
          let K := n + 1 + w.length + (b :: v).length + 4
          obtain ⟨t, ht, hrun⟩ := count_tail_success n 1 K w [] b v
            (by simp only [List.length_cons] at hc; omega)
            (by simp only [K, List.length_cons, List.length_nil]; omega)
          simp only [List.map_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append] at hrun
          have hstep := count_first_start n w b v
          simp only [List.append_assoc, List.cons_append] at hstep
          have hs : 2 * (n + w.length) + 10 ≤ 32 * K := by
            simp only [K, List.length_cons]; omega
          refine ⟨2 * (n + w.length) + 10 + t, ?_, ?_⟩
          · change _ ≤ 64 * (n + 2) * K
            calc
              _ ≤ 32 * K + 32 * (n + 1) * K := Nat.add_le_add hs ht
              _ = 32 * (n + 2) * K := by simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
              _ ≤ 64 * (n + 2) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right (n + 2) (by decide))
          · have h := trans hstep hrun
            simpa only [List.map_nil, List.nil_append, List.append_assoc, List.cons_append,
              Nat.add_comm] using h

/-- Both shorter and longer certificates reject, including empty certificates
and the zero-input case. No gate result or certificate content is assumed. -/
theorem count_reject (n : Nat) (w cert : Word) (hc : cert.length ≠ n) :
    ∃ t, t ≤ 64 * (n + 1) * (n + w.length + cert.length + 4) ∧
      Run candidate (cfg 17 [.blank]
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool)) t false := by
  cases n with
  | zero =>
      cases cert with
      | nil => exact False.elim (hc rfl)
      | cons b v =>
          exact ⟨w.length + 3, by simp only [List.length_cons]; omega,
            by simpa only [ones, List.replicate_zero, List.nil_append] using count_zero_long w b v⟩
  | succ n =>
      let K := n + 1 + w.length + cert.length + 4
      have hm : 32 * K ≤ 64 * (n + 2) * K :=
        Nat.mul_le_mul_right K (by omega)
      cases cert with
      | nil =>
          have hs : n + w.length + 4 ≤ 32 * K := by simp only [K, List.length_nil]; omega
          exact ⟨n + w.length + 4, Nat.le_trans hs hm,
            by simpa only [List.map_nil] using count_first_short n w⟩
      | cons b v =>
          obtain ⟨t, ht, hrun⟩ := count_tail_reject n 1 K w [] b v
            (by simp only [List.length_cons] at hc; omega)
            (by simp only [K, List.length_cons, List.length_nil]; omega)
          simp only [List.map_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append] at hrun
          have hstep := count_first_start n w b v
          simp only [List.append_assoc, List.cons_append] at hstep
          have hs : 2 * (n + w.length) + 10 ≤ 32 * K := by
            simp only [K, List.length_cons]; omega
          refine ⟨2 * (n + w.length) + 10 + t, ?_, ?_⟩
          · change _ ≤ 64 * (n + 2) * K
            calc
              _ ≤ 32 * K + 32 * (n + 1) * K := Nat.add_le_add hs ht
              _ = 32 * (n + 2) * K := by simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
              _ ≤ 64 * (n + 2) * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right (n + 2) (by decide))
          · simpa only [List.map_nil, List.nil_append, List.append_assoc, List.cons_append] using hstep.run hrun



/-! Unary wire lookup on the charged finite evaluator table. -/

inductive LookupKind where
  | first | secondFalse | secondTrue
  deriving DecidableEq

def lookupPrefix : LookupKind → Nat → List Symbol
  | .first, _ => []
  | _, j => ones j ++ [.zero]

def lookupInit : LookupKind → Nat
  | .first => 41
  | .secondFalse => 51
  | .secondTrue => 62

def lookupBackSep : LookupKind → Nat
  | .first => 38
  | .secondFalse => 48
  | .secondTrue => 59

def lookupBackGate : LookupKind → Nat
  | .first => 37
  | .secondFalse => 47
  | .secondTrue => 58

def lookupUnary : LookupKind → Nat
  | .first => 46
  | .secondFalse => 57
  | .secondTrue => 68

def lookupSeekIncrement : LookupKind → Nat
  | .first => 44
  | .secondFalse => 54
  | .secondTrue => 65

def lookupCursorIncrement : LookupKind → Nat
  | .first => 39
  | .secondFalse => 49
  | .secondTrue => 60

def lookupMarkNext : LookupKind → Nat
  | .first => 43
  | .secondFalse => 53
  | .secondTrue => 64

def lookupSkipFirst : LookupKind → Nat
  | .first => 46
  | .secondFalse => 56
  | .secondTrue => 67

def lookupSeekRead : LookupKind → Nat
  | .first => 45
  | .secondFalse => 55
  | .secondTrue => 66

def lookupCursorRead : LookupKind → Nat
  | .first => 40
  | .secondFalse => 50
  | .secondTrue => 61

def lookupReadValue : LookupKind → Bool → Bool
  | .first, b => b
  | .secondFalse, _ => true
  | .secondTrue, b => !b

def restoreSep (k : LookupKind) (b : Bool) : Nat :=
  match k, lookupReadValue k b with
  | .first, false => 31
  | .first, true => 34
  | _, false => 70
  | _, true => 74

def restoreGate (k : LookupKind) (b : Bool) : Nat :=
  match k, lookupReadValue k b with
  | .first, false => 30
  | .first, true => 33
  | _, false => 69
  | _, true => 73

def restoreUnary (k : LookupKind) (b : Bool) : Nat :=
  match k, lookupReadValue k b with
  | .first, false => 32
  | .first, true => 35
  | _, false => 72
  | _, true => 76

def restoreSkipFirst (k : LookupKind) (b : Bool) : Nat :=
  match k, lookupReadValue k b with
  | .first, _ => restoreUnary k b
  | _, false => 71
  | _, true => 75

def lookupExit (k : LookupKind) (b : Bool) : Nat :=
  match k, lookupReadValue k b with
  | .first, false => 51
  | .first, true => 62
  | _, false => 6
  | _, true => 8

theorem bitR (q : Nat) (w : Word) (L R : List Symbol)
    (h : ∀ b, candidate.instruction q (Symbol.ofBool b) = .move q (Symbol.ofBool b) .right) :
    Rch (cfg q L (w.map Symbol.ofBool ++ R)) w.length
      (cfg q ((w.map Symbol.ofBool).reverse ++ L) R) := by
  simpa only [List.length_map] using walkR q (w.map Symbol.ofBool) L R (by
    intro a ha; obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha; exact h b)

theorem bits_back (q q' : Nat) (marker : Symbol) (w : Word) (L : List Symbol)
    (a : Symbol) (R : List Symbol)
    (ha : candidate.instruction q a = .move q' a .left)
    (hw : ∀ b, candidate.instruction q' (Symbol.ofBool b) = .move q' (Symbol.ofBool b) .left) :
    Rch (cfg q ((w.map Symbol.ofBool).reverse ++ marker :: L) (a :: R))
      (w.length + 1) (cfg q' L (marker :: w.map Symbol.ofBool ++ a :: R)) := by
  simpa only [List.reverse_reverse, List.length_reverse, List.length_map] using
    rewind q q' marker a (w.map Symbol.ofBool).reverse L R ha (by
      intro a ha; obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha); exact hw b)

/-- Returning to the active counter crosses only the first operand and the
already consumed ticks. The blank gate marker is the unique left boundary. -/
theorem lookup_resume (k : LookupKind) (j p : Nat) (L R : List Symbol) :
    Rch (cfg (lookupBackGate k) L
      (.blank :: lookupPrefix k j ++ marks p ++ R))
      (1 + (lookupPrefix k j).length + p)
      (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L) R) := by
  have hm := walkR (lookupUnary k) (marks p)
    ((lookupPrefix k j).reverse ++ .blank :: L) R (by
      intro a ha; have := marks_mem ha; subst a; cases k <;> rfl)
  simp only [marks, List.reverse_replicate, List.length_replicate] at hm
  cases k with
  | first => simpa [lookupPrefix, lookupBackGate, lookupUnary, marks, Nat.add_comm] using R1 rfl hm
  | secondFalse =>
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.singleton_append, List.reverse_replicate, List.cons_append, List.append_assoc] at hm
      have hp := walkR 56 (ones j) (.blank :: L)
        (.zero :: marks p ++ R) (by intro a ha; have := ones_mem ha; subst a; rfl)
      have hz := R1 (q := 56) (a := .zero) rfl hm
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_replicate,
        List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append,
        List.append_assoc, List.length_replicate] at hp hz ⊢
      simpa [marks, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using R1 rfl (trans hp hz)
  | secondTrue =>
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.singleton_append, List.reverse_replicate, List.cons_append, List.append_assoc] at hm
      have hp := walkR 67 (ones j) (.blank :: L)
        (.zero :: marks p ++ R) (by intro a ha; have := ones_mem ha; subst a; rfl)
      have hz := R1 (q := 67) (a := .zero) rfl hm
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_replicate,
        List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append,
        List.append_assoc, List.length_replicate] at hp hz ⊢
      simpa [marks, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using R1 rfl (trans hp hz)

theorem lookup_return (k : LookupKind) (j p : Nat) (r u : Word) (b : Bool)
    (L R : List Symbol) :
    Rch (cfg (lookupBackSep k)
      ((u.map Symbol.ofBool).reverse ++ .separator :: (r.map Symbol.ofBool).reverse ++
        marks p ++ (lookupPrefix k j).reverse ++ .blank :: L) (Symbol.ofBool b :: R))
      (u.length + r.length + 2 * p + 2 * (lookupPrefix k j).length + 3)
      (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
        (r.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R)) := by
  have h1 := bits_back (lookupBackSep k) (lookupBackSep k) .separator u
    ((r.map Symbol.ofBool).reverse ++ marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
    (Symbol.ofBool b) R (by cases k <;> cases b <;> rfl) (by intro b; cases k <;> cases b <;> rfl)
  have h2 := rewind (lookupBackSep k) (lookupBackGate k) .blank .separator
    ((r.map Symbol.ofBool).reverse ++ marks p ++ (lookupPrefix k j).reverse) L
    ((u ++ [b]).map Symbol.ofBool ++ R) (by cases k <;> rfl) (by
      intro a ha
      try simp only [List.append_assoc] at ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> cases k <;> rfl
      · rcases List.mem_append.mp ha with ha | ha
        · have := marks_mem ha; subst a; cases k <;> rfl
        · cases k <;> simp only [lookupPrefix] at ha
          · simp at ha
          · rcases List.mem_reverse.mp ha |> List.mem_append.mp with ha | ha
            · have := ones_mem ha; subst a; rfl
            · simp at ha; subst a; rfl
          · rcases List.mem_reverse.mp ha |> List.mem_append.mp with ha | ha
            · have := ones_mem ha; subst a; rfl
            · simp at ha; subst a; rfl)
  have h3 := lookup_resume k j p L
    (r.map Symbol.ofBool ++ .separator :: (u ++ [b]).map Symbol.ofBool ++ R)
  simp only [marks, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_reverse, List.reverse_replicate, List.length_append, List.length_reverse,
    List.length_map, List.length_replicate, List.singleton_append, List.cons_append,
    List.append_assoc] at h1 h2 h3 ⊢
  have h := trans h1 (trans h2 h3)
  have ht : (u.length + 1) + ((r.length + (p + (lookupPrefix k j).length) + 1) +
      (1 + (lookupPrefix k j).length + p)) =
      u.length + r.length + 2 * p + 2 * (lookupPrefix k j).length + 3 := by omega
  rw [ht] at h
  exact h

/-- One consumed unary tick advances the marked cursor by exactly one wire,
restoring the old cursor's Boolean value. All circuit cells stay in place. -/
theorem lookup_advance (k : LookupKind) (j p n : Nat) (w u : Word) (b c : Bool)
    (v : Word) (L T : List Symbol) :
    Rch (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
      (ones (n + 1) ++ .zero :: w.map Symbol.ofBool ++ .separator ::
        u.map Symbol.ofBool ++ cursor b :: (c :: v).map Symbol.ofBool ++ T))
      (2 * (n + w.length + u.length + p + (lookupPrefix k j).length) + 11)
      (cfg (lookupUnary k) (marks (p + 1) ++ (lookupPrefix k j).reverse ++ .blank :: L)
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator ::
          (u ++ [b]).map Symbol.ofBool ++ cursor c :: v.map Symbol.ofBool ++ T)) := by
  let r : Word := List.replicate n true ++ false :: w
  have hr : r.map Symbol.ofBool = ones n ++ .zero :: w.map Symbol.ofBool := by
    simp [r, ones, Symbol.ofBool]
  have h1 := bitR (lookupSeekIncrement k) r
    (marks (p + 1) ++ (lookupPrefix k j).reverse ++ .blank :: L)
    (.separator :: u.map Symbol.ofBool ++ cursor b :: (c :: v).map Symbol.ofBool ++ T)
    (by intro b; cases k <;> cases b <;> rfl)
  have h2 := bitR (lookupCursorIncrement k) u
    (.separator :: (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++
      (lookupPrefix k j).reverse ++ .blank :: L)
    (cursor b :: (c :: v).map Symbol.ofBool ++ T) (by intro b; cases k <;> cases b <;> rfl)
  have h3 := lookup_return k j (p + 1) r u b L (cursor c :: v.map Symbol.ofBool ++ T)
  have h4 := L1 (q := lookupMarkNext k) (a := Symbol.ofBool c) (w := cursor c)
    (by cases k <;> cases c <;> rfl) h3
  have h5 := R1 (q := lookupCursorIncrement k) (a := cursor b) (w := Symbol.ofBool b)
    (by cases k <;> cases b <;> rfl) h4
  simp only [List.map_cons, List.append_assoc, List.cons_append] at h1 h2 h5
  have h6 := trans h2 h5
  have h7 := R1 (q := lookupSeekIncrement k) (a := .separator) (by cases k <;> rfl) h6
  have h8 := trans h1 h7
  have h9 := R1 (q := lookupUnary k) (a := .one) (w := .separator) (by cases k <;> rfl) h8
  have hp : .separator :: marks p = marks (p + 1) := by simp [marks, List.replicate_succ]
  have hn : .one :: ones n = ones (n + 1) := by simp [ones, List.replicate_succ]
  simp only [← hp, ← hn, List.cons_append, hr, List.append_assoc] at h9 ⊢
  have ht : r.length + (u.length +
      (u.length + r.length + 2 * (p + 1) + 2 * (lookupPrefix k j).length + 3 + 1 + 1) + 1) + 1 =
      2 * (n + w.length + u.length + p + (lookupPrefix k j).length) + 11 := by
    simp only [r, List.length_append, List.length_replicate, List.length_cons]; omega
  rw [ht] at h9
  exact h9

/-- Running out of wires while consuming an index rejects with a charged
halting instruction, including a false cursor immediately before the end. -/
theorem lookup_short (k : LookupKind) (j p n : Nat) (w u : Word) (b : Bool)
    (L T : List Symbol) (hT : T = [] ∨ T = [.blank]) :
    Run candidate (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
      (ones (n + 1) ++ .zero :: w.map Symbol.ofBool ++ .separator ::
        u.map Symbol.ofBool ++ cursor b :: T)) (n + w.length + u.length + 5) false := by
  let r : Word := List.replicate n true ++ false :: w
  have hr : r.map Symbol.ofBool = ones n ++ .zero :: w.map Symbol.ofBool := by simp [r, ones, Symbol.ofBool]
  have h1 := bitR (lookupSeekIncrement k) r
    (marks (p + 1) ++ (lookupPrefix k j).reverse ++ .blank :: L)
    (.separator :: u.map Symbol.ofBool ++ cursor b :: T) (by intro b; cases k <;> cases b <;> rfl)
  have h2 := bitR (lookupCursorIncrement k) u
    (.separator :: (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++
      (lookupPrefix k j).reverse ++ .blank :: L) (cursor b :: T)
    (by intro b; cases k <;> cases b <;> rfl)
  have h3 : Run candidate (cfg (lookupMarkNext k)
      (Symbol.ofBool b :: (u.map Symbol.ofBool).reverse ++ .separator ::
        (r.map Symbol.ofBool).reverse ++ marks (p + 1) ++
          (lookupPrefix k j).reverse ++ .blank :: L) T) 1 false := Run.halt (by rcases hT with rfl | rfl <;> cases k <;> rfl)
  have h4 := Run.next (stepR (q := lookupCursorIncrement k) (a := cursor b)
    (w := Symbol.ofBool b) (by cases k <;> cases b <;> rfl) _ _) h3
  change Run candidate (cfg (lookupCursorIncrement k)
    ((u.map Symbol.ofBool).reverse ++ .separator :: (r.map Symbol.ofBool).reverse ++
      marks (p + 1) ++ (lookupPrefix k j).reverse ++ .blank :: L) (cursor b :: T)) (1 + 1) false at h4
  simp only [List.append_assoc, List.cons_append] at h1 h2 h4
  have h5 := h2.run h4
  have h6 := Run.next (stepR (q := lookupSeekIncrement k) (a := .separator) (by cases k <;> rfl) _ _) h5
  have h7 := h1.run h6
  have h8 := Run.next (stepR (q := lookupUnary k) (a := .one) (w := .separator)
    (by cases k <;> rfl) _ _) h7
  have ht : r.length + (u.length + (1 + 1) + 1) + 1 = n + w.length + u.length + 5 := by
    simp only [r, List.length_append, List.length_replicate, List.length_cons]; omega
  rw [ht] at h8
  simpa only [hr, ones, marks, List.replicate_succ, List.append_eq, List.cons_append,
    List.length_map, List.length_append, List.length_cons, List.length_replicate,
    List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h8

theorem rewindWrite (q q' : Nat) (marker a write : Symbol) (w L R : List Symbol)
    (ha : candidate.instruction q a = .move q' write .left)
    (hw : ∀ b ∈ w, candidate.instruction q' b = .move q' b .left) :
    Rch (cfg q (w ++ marker :: L) (a :: R)) (w.length + 1)
      (cfg q' L (marker :: w.reverse ++ write :: R)) := by
  cases w with
  | nil => exact L1 ha (Reaches.refl _)
  | cons b w => simpa [Nat.add_comm] using L1 ha (walkL q' marker L w b (write :: R) hw)

theorem lookup_prefix_mem {k : LookupKind} {j : Nat} {a : Symbol}
    (h : a ∈ lookupPrefix k j) : a = .zero ∨ a = .one := by
  cases k <;> simp only [lookupPrefix] at h
  · simp at h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inr (ones_mem h)
    · simp at h; exact Or.inl h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inr (ones_mem h)
    · simp at h; exact Or.inl h

theorem restore_ticks (k : LookupKind) (b : Bool) (p : Nat) (L R : List Symbol) :
    Rch (cfg (restoreUnary k b) L (marks p ++ R)) p
      (cfg (restoreUnary k b) (ones p ++ L) R) := by
  induction p generalizing L with
  | zero => exact Reaches.refl _
  | succ p ih =>
      have h := R1 (q := restoreUnary k b) (a := .separator) (w := .one)
        (by cases k <;> cases b <;> rfl) (ih (.one :: L))
      have he : ones (p + 1) ++ L = ones p ++ .one :: L := by
        simp only [ones, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [he]
      simpa only [marks, List.replicate_succ, List.cons_append] using h

theorem restore_resume (k : LookupKind) (b : Bool) (j p : Nat) (L R : List Symbol) :
    Rch (cfg (restoreGate k b) L (.blank :: lookupPrefix k j ++ marks p ++ R))
      (1 + (lookupPrefix k j).length + p)
      (cfg (restoreUnary k b) (ones p ++ (lookupPrefix k j).reverse ++ .blank :: L) R) := by
  have hm := restore_ticks k b p ((lookupPrefix k j).reverse ++ .blank :: L) R
  cases k with
  | first =>
      have h := R1 (q := restoreGate .first b) (a := .blank) (by cases b <;> rfl) hm
      simpa [lookupPrefix, restoreGate, restoreUnary, lookupReadValue, Nat.add_comm] using h
  | secondFalse =>
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.singleton_append, List.reverse_replicate, List.cons_append, List.append_assoc] at hm
      have hp := walkR (restoreSkipFirst .secondFalse b) (ones j) (.blank :: L)
        (.zero :: marks p ++ R) (by intro a ha; have := ones_mem ha; subst a; cases b <;> rfl)
      have hz := R1 (q := restoreSkipFirst .secondFalse b) (a := .zero) (by cases b <;> rfl) hm
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_replicate,
        List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append,
        List.append_assoc, List.length_replicate] at hp hz ⊢
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using R1 (by cases b <;> rfl) (trans hp hz)
  | secondTrue =>
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.singleton_append, List.reverse_replicate, List.cons_append, List.append_assoc] at hm
      have hp := walkR (restoreSkipFirst .secondTrue b) (ones j) (.blank :: L)
        (.zero :: marks p ++ R) (by intro a ha; have := ones_mem ha; subst a; cases b <;> rfl)
      have hz := R1 (q := restoreSkipFirst .secondTrue b) (a := .zero) (by cases b <;> rfl) hm
      simp only [lookupPrefix, ones, List.reverse_append, List.reverse_replicate,
        List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append,
        List.append_assoc, List.length_replicate] at hp hz ⊢
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using R1 (by cases b <;> rfl) (trans hp hz)

/-- Reading the cursor returns the selected wire value (or the stored NAND
for operand two), restores the unary operand, and preserves every wire bit. -/
theorem lookup_read (k : LookupKind) (j p : Nat) (w u : Word) (b : Bool)
    (v : Word) (L T : List Symbol) :
    Rch (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
      (.zero :: w.map Symbol.ofBool ++ .separator :: u.map Symbol.ofBool ++ cursor b :: v.map Symbol.ofBool ++ T))
      (2 * (w.length + u.length + p + (lookupPrefix k j).length) + 7)
      (cfg (lookupExit k b) (.zero :: ones p ++ (lookupPrefix k j).reverse ++ .blank :: L)
        (w.map Symbol.ofBool ++ .separator :: (u ++ b :: v).map Symbol.ofBool ++ T)) := by
  have h1 := bitR (lookupSeekRead k) w
    (.zero :: marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
    (.separator :: u.map Symbol.ofBool ++ cursor b :: v.map Symbol.ofBool ++ T)
    (by intro b; cases k <;> cases b <;> rfl)
  have h2 := bitR (lookupCursorRead k) u
    (.separator :: (w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
    (cursor b :: v.map Symbol.ofBool ++ T) (by intro b; cases k <;> cases b <;> rfl)
  have h3 := rewindWrite (lookupCursorRead k) (restoreSep k b) .separator (cursor b) (Symbol.ofBool b)
    (u.map Symbol.ofBool).reverse
    ((w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
    (v.map Symbol.ofBool ++ T) (by cases k <;> cases b <;> rfl) (by
      intro a ha; rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> cases k <;> cases b <;> rfl)
  have h4 := rewind (restoreSep k b) (restoreGate k b) .blank .separator
    ((w.map Symbol.ofBool).reverse ++ .zero :: marks p ++ (lookupPrefix k j).reverse) L
    ((u ++ b :: v).map Symbol.ofBool ++ T) (by cases k <;> cases b <;> rfl) (by
      intro a ha
      try simp only [List.append_assoc] at ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> cases k <;> cases b <;> rfl
      · rcases List.mem_cons.mp ha with ha | ha
        · subst a; cases k <;> cases b <;> rfl
        · rcases List.mem_append.mp ha with ha | ha
          · have := marks_mem ha; subst a; cases k <;> cases b <;> rfl
          · rcases lookup_prefix_mem (List.mem_reverse.mp ha) with rfl | rfl <;> cases k <;> cases b <;> rfl)
  have h5 := restore_resume k b j p L
    (.zero :: w.map Symbol.ofBool ++ .separator :: (u ++ b :: v).map Symbol.ofBool ++ T)
  have h6 : Rch (cfg (restoreUnary k b) (ones p ++ (lookupPrefix k j).reverse ++ .blank :: L)
      (.zero :: w.map Symbol.ofBool ++ .separator :: (u ++ b :: v).map Symbol.ofBool ++ T)) 1
      (cfg (lookupExit k b) (.zero :: ones p ++ (lookupPrefix k j).reverse ++ .blank :: L)
        (w.map Symbol.ofBool ++ .separator :: (u ++ b :: v).map Symbol.ofBool ++ T)) :=
    R1 (by cases k <;> cases b <;> rfl) (Reaches.refl _)
  simp only [List.map_append, List.map_cons, List.reverse_reverse, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.reverse_replicate, List.length_reverse,
    List.length_map, List.length_append, List.length_cons, List.length_nil, marks,
    List.length_replicate, List.singleton_append, List.cons_append, List.append_assoc] at h1 h2 h3 h4 h5 h6 ⊢
  have h := trans h3 (trans h4 (trans h5 h6))
  have h' := trans h2 h
  have h'' := R1 (q := lookupSeekRead k) (a := .separator) (by cases k <;> rfl) h'
  have h''' := trans h1 h''
  have h'''' := R1 (q := lookupUnary k) (a := .zero) (by cases k <;> rfl) h'''
  have ht : (w.length + (u.length + ((u.length + 1) +
      ((w.length + (p + (lookupPrefix k j).length + 1) + 1) +
        ((1 + (lookupPrefix k j).length + p) + 1))) + 1) + 1) =
      2 * (w.length + u.length + p + (lookupPrefix k j).length) + 7 := by omega
  rw [ht] at h''''
  exact h''''

def lookupMarkInitial : LookupKind → Nat
  | .first => 42
  | .secondFalse => 52
  | .secondTrue => 63

theorem lookup_initial (k : LookupKind) (j : Nat) (w : Word) (b : Bool) (v : Word)
    (L T : List Symbol) :
    Rch (cfg (lookupInit k) ((lookupPrefix k j).reverse ++ .blank :: L)
      (w.map Symbol.ofBool ++ .separator :: (b :: v).map Symbol.ofBool ++ T))
      (2 * w.length + 2 * (lookupPrefix k j).length + 4)
      (cfg (lookupUnary k) ((lookupPrefix k j).reverse ++ .blank :: L)
        (w.map Symbol.ofBool ++ .separator :: cursor b :: v.map Symbol.ofBool ++ T)) := by
  have h1 := bitR (lookupInit k) w ((lookupPrefix k j).reverse ++ .blank :: L)
    (.separator :: (b :: v).map Symbol.ofBool ++ T) (by intro b; cases k <;> cases b <;> rfl)
  have h2 := rewind (lookupBackSep k) (lookupBackGate k) .blank .separator
    ((w.map Symbol.ofBool).reverse ++ (lookupPrefix k j).reverse) L
    (cursor b :: v.map Symbol.ofBool ++ T) (by cases k <;> rfl) (by
      intro a ha
      try simp only [List.append_assoc] at ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> cases k <;> rfl
      · rcases lookup_prefix_mem (List.mem_reverse.mp ha) with rfl | rfl <;> cases k <;> rfl)
  have h3 := lookup_resume k j 0 L (w.map Symbol.ofBool ++ .separator :: cursor b :: v.map Symbol.ofBool ++ T)
  simp only [List.map_cons, List.reverse_append, List.reverse_reverse, List.length_append,
    List.length_reverse, List.length_map, marks, List.replicate_zero, List.nil_append,
    List.cons_append, List.append_assoc, Nat.add_zero] at h1 h2 h3 ⊢
  have h4 := L1 (q := lookupMarkInitial k) (a := Symbol.ofBool b) (w := cursor b)
    (by cases k <;> cases b <;> rfl) (trans h2 h3)
  have h5 := R1 (q := lookupInit k) (a := .separator) (by cases k <;> rfl) h4
  have h := trans h1 h5
  have ht : w.length + ((w.length + (lookupPrefix k j).length + 1 +
      (1 + (lookupPrefix k j).length)) + 1 + 1) =
      2 * w.length + 2 * (lookupPrefix k j).length + 4 := by omega
  rw [ht] at h
  exact h

theorem lookup_empty (k : LookupKind) (j : Nat) (w : Word) (L T : List Symbol)
    (hT : T = [] ∨ T = [.blank]) :
    Run candidate (cfg (lookupInit k) ((lookupPrefix k j).reverse ++ .blank :: L)
      (w.map Symbol.ofBool ++ .separator :: T)) (w.length + 2) false := by
  have h1 := bitR (lookupInit k) w ((lookupPrefix k j).reverse ++ .blank :: L)
    (.separator :: T) (by intro b; cases k <;> cases b <;> rfl)
  have h2 : Run candidate (cfg (lookupMarkInitial k)
      (.separator :: (w.map Symbol.ofBool).reverse ++ (lookupPrefix k j).reverse ++ .blank :: L) T) 1 false :=
    Run.halt (by rcases hT with rfl | rfl <;> cases k <;> rfl)
  have h3 := Run.next (stepR (q := lookupInit k) (a := .separator) (by cases k <;> rfl) _ _) h2
  try simp only [List.cons_append, List.append_assoc] at h1
  simp only [List.append_eq, List.cons_append, List.append_assoc] at h3
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h1.run h3


open Issue532.Circuits

/-- The counter and cursor move in lockstep for an arbitrary valid index.
The cost bounds real instructions, including repeated returns over used ticks. -/
theorem lookup_tail_success (n : Nat) : ∀ (k : LookupKind) (j p K : Nat)
    (w u : Word) (b : Bool) (v : Word) (L T : List Symbol),
    n < (b :: v).length →
    p + n + w.length + u.length + v.length + (lookupPrefix k j).length + 4 ≤ K →
    ∃ t, t ≤ 32 * (n + 1) * K ∧
      Rch (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator ::
          u.map Symbol.ofBool ++ cursor b :: v.map Symbol.ofBool ++ T)) t
        (cfg (lookupExit k (wire (b :: v) n))
          (.zero :: ones (p + n) ++ (lookupPrefix k j).reverse ++ .blank :: L)
          (w.map Symbol.ofBool ++ .separator :: (u ++ b :: v).map Symbol.ofBool ++ T)) := by
  induction n with
  | zero =>
      intro k j p K w u b v L T hn hK
      refine ⟨2 * (w.length + u.length + p + (lookupPrefix k j).length) + 7, by omega, ?_⟩
      simpa only [ones, List.replicate_zero, List.nil_append, Nat.add_zero, wire, List.getD_cons_zero] using
        lookup_read k j p w u b v L T
  | succ n ih =>
      intro k j p K w u b v L T hn hK
      cases v with
      | nil => simp only [List.length_cons, List.length_nil] at hn; omega
      | cons c v =>
          obtain ⟨t, ht, hrun⟩ := ih k j (p + 1) K w (u ++ [b]) c v L T
            (by simp only [List.length_cons] at hn ⊢; omega)
            (by simp only [List.length_cons, List.length_append, List.length_nil] at hK ⊢; omega)
          have hstep := lookup_advance k j p n w u b c v L T
          have hs : 2 * (n + w.length + u.length + p + (lookupPrefix k j).length) + 11 ≤ 32 * K := by
            simp only [List.length_cons] at hK; omega
          refine ⟨2 * (n + w.length + u.length + p + (lookupPrefix k j).length) + 11 + t, ?_, ?_⟩
          · calc
              _ ≤ 32 * K + 32 * (n + 1) * K := Nat.add_le_add hs ht
              _ = 32 * (n + 1 + 1) * K := by simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
          · simpa only [wire, List.getD_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm, List.map_cons, List.map_append, List.map_nil,
              List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using trans hstep hrun

/-- Every unavailable index rejects; the proof is universal, including the
implicit and explicit blank representations at the end of the wire list. -/
theorem lookup_tail_reject (n : Nat) : ∀ (k : LookupKind) (j p K : Nat)
    (w u : Word) (b : Bool) (v : Word) (L T : List Symbol),
    (b :: v).length ≤ n → (T = [] ∨ T = [.blank]) →
    p + n + w.length + u.length + v.length + (lookupPrefix k j).length + 4 ≤ K →
    ∃ t, t ≤ 32 * (n + 1) * K ∧
      Run candidate (cfg (lookupUnary k) (marks p ++ (lookupPrefix k j).reverse ++ .blank :: L)
        (ones n ++ .zero :: w.map Symbol.ofBool ++ .separator ::
          u.map Symbol.ofBool ++ cursor b :: v.map Symbol.ofBool ++ T)) t false := by
  induction n with
  | zero => intro k j p K w u b v L T hn; simp at hn
  | succ n ih =>
      intro k j p K w u b v L T hn hT hK
      cases v with
      | nil =>
          have hs : n + w.length + u.length + 5 ≤ 32 * K := by
            simp only [List.length_nil] at hK; omega
          refine ⟨n + w.length + u.length + 5,
            Nat.le_trans hs (Nat.mul_le_mul_right K (by omega)), ?_⟩
          simpa only [List.map_nil, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc] using lookup_short k j p n w u b L T hT
      | cons c v =>
          obtain ⟨t, ht, hrun⟩ := ih k j (p + 1) K w (u ++ [b]) c v L T
            (by simp only [List.length_cons] at hn ⊢; omega) hT
            (by simp only [List.length_cons, List.length_append, List.length_nil] at hK ⊢; omega)
          have hstep := lookup_advance k j p n w u b c v L T
          have hs : 2 * (n + w.length + u.length + p + (lookupPrefix k j).length) + 11 ≤ 32 * K := by
            simp only [List.length_cons] at hK; omega
          refine ⟨2 * (n + w.length + u.length + p + (lookupPrefix k j).length) + 11 + t, ?_, ?_⟩
          · calc
              _ ≤ 32 * K + 32 * (n + 1) * K := Nat.add_le_add hs ht
              _ = 32 * (n + 1 + 1) * K := by simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
          · simpa only [Nat.succ_eq_add_one, List.map_cons, List.map_append, List.map_nil,
              List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using hstep.run hrun


theorem lookup_success (k : LookupKind) (j i K : Nat) (w v : Word)
    (L T : List Symbol) (hi : i < v.length)
    (hK : i + w.length + v.length + (lookupPrefix k j).length + 4 ≤ K) :
    ∃ t, t ≤ 64 * (i + 1) * K ∧
      Rch (cfg (lookupInit k) ((lookupPrefix k j).reverse ++ .blank :: L)
        (ones i ++ .zero :: w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T)) t
        (cfg (lookupExit k (wire v i)) (.zero :: ones i ++ (lookupPrefix k j).reverse ++ .blank :: L)
          (w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T)) := by
  cases v with
  | nil => simp at hi
  | cons b v =>
      let r : Word := List.replicate i true ++ false :: w
      have hr : r.map Symbol.ofBool = ones i ++ .zero :: w.map Symbol.ofBool := by simp [r, ones, Symbol.ofBool]
      have hinit := lookup_initial k j r b v L T
      simp only [hr, List.append_assoc, List.cons_append] at hinit
      obtain ⟨t, ht, hrun⟩ := lookup_tail_success i k j 0 K w [] b v L T hi (by
        simp only [List.length_cons, List.length_nil] at hK ⊢; omega)
      have hs : 2 * r.length + 2 * (lookupPrefix k j).length + 4 ≤ 32 * K := by
        simp only [r, List.length_append, List.length_replicate, List.length_cons] at *; omega
      refine ⟨2 * r.length + 2 * (lookupPrefix k j).length + 4 + t, ?_, ?_⟩
      · calc
          _ ≤ 32 * K + 32 * (i + 1) * K := Nat.add_le_add hs ht
          _ ≤ 32 * (i + 1) * K + 32 * (i + 1) * K :=
            Nat.add_le_add (Nat.mul_le_mul_right K (by omega)) (Nat.le_refl _)
          _ = 64 * (i + 1) * K := by simp only [← Nat.add_mul] <;> omega
      · simp only [marks, List.replicate_zero, List.nil_append, List.map_nil,
          List.map_cons, Nat.zero_add, List.append_assoc, List.cons_append] at hrun
        simpa only [hr, List.map_cons, List.append_assoc, List.cons_append] using trans hinit hrun

theorem lookup_reject (k : LookupKind) (j i K : Nat) (w v : Word)
    (L T : List Symbol) (hi : v.length ≤ i) (hT : T = [] ∨ T = [.blank])
    (hK : i + w.length + v.length + (lookupPrefix k j).length + 4 ≤ K) :
    ∃ t, t ≤ 64 * (i + 1) * K ∧
      Run candidate (cfg (lookupInit k) ((lookupPrefix k j).reverse ++ .blank :: L)
        (ones i ++ .zero :: w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T)) t false := by
  let r : Word := List.replicate i true ++ false :: w
  have hr : r.map Symbol.ofBool = ones i ++ .zero :: w.map Symbol.ofBool := by simp [r, ones, Symbol.ofBool]
  cases v with
  | nil =>
      have h := lookup_empty k j r L T hT
      refine ⟨r.length + 2, ?_, ?_⟩
      · have hs : r.length + 2 ≤ 64 * K := by
          simp only [r, List.length_append, List.length_replicate, List.length_cons, List.length_nil] at *; omega
        exact Nat.le_trans hs (Nat.mul_le_mul_right K (by omega))
      · simpa only [hr, List.map_nil, List.nil_append, List.append_assoc, List.cons_append] using h
  | cons b v =>
      have hinit := lookup_initial k j r b v L T
      simp only [hr, List.append_assoc, List.cons_append] at hinit
      obtain ⟨t, ht, hrun⟩ := lookup_tail_reject i k j 0 K w [] b v L T hi hT (by
        simp only [List.length_cons, List.length_nil] at hK ⊢; omega)
      have hs : 2 * r.length + 2 * (lookupPrefix k j).length + 4 ≤ 32 * K := by
        simp only [r, List.length_append, List.length_replicate, List.length_cons] at *; omega
      refine ⟨2 * r.length + 2 * (lookupPrefix k j).length + 4 + t, ?_, ?_⟩
      · calc
          _ ≤ 32 * K + 32 * (i + 1) * K := Nat.add_le_add hs ht
          _ ≤ 32 * (i + 1) * K + 32 * (i + 1) * K :=
            Nat.add_le_add (Nat.mul_le_mul_right K (by omega)) (Nat.le_refl _)
          _ = 64 * (i + 1) * K := by simp only [← Nat.add_mul] <;> omega
      · simp only [marks, List.replicate_zero, List.nil_append, List.map_nil,
          List.map_cons, List.append_assoc, List.cons_append] at hrun
        simpa only [hr, List.map_cons, List.append_assoc, List.cons_append] using hinit.run hrun



/-! Restoring a finished NAND gate and appending its output on the tape. -/
def appendSep (b : Bool) : Nat := if b then 8 else 6
def appendEnd (b : Bool) : Nat := if b then 7 else 5

theorem append_gate (b : Bool) (i j : Nat) (w v : Word) (L T : List Symbol)
    (hT : T = [] ∨ T = [.blank]) :
    Rch (cfg (appendSep b) (.zero :: ones j ++ .zero :: ones i ++ .blank :: L)
      (w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T))
      (2 * w.length + 2 * v.length + 2 * i + 2 * j + 8)
      (cfg 36 (.zero :: ones j ++ .zero :: ones i ++ .one :: L)
        (w.map Symbol.ofBool ++ .separator :: (v ++ [b]).map Symbol.ofBool)) := by
  have h1 := bitR (appendSep b) w (.zero :: ones j ++ .zero :: ones i ++ .blank :: L)
    (.separator :: v.map Symbol.ofBool ++ T) (by intro a; cases b <;> cases a <;> rfl)
  have h2 := bitR (appendEnd b) v
    (.separator :: (w.map Symbol.ofBool).reverse ++ .zero :: ones j ++ .zero :: ones i ++ .blank :: L)
    T (by intro a; cases b <;> cases a <;> rfl)
  have h3 := rewindWrite (appendEnd b) 4 .separator .blank (Symbol.ofBool b)
    (v.map Symbol.ofBool).reverse
    ((w.map Symbol.ofBool).reverse ++ .zero :: ones j ++ .zero :: ones i ++ .blank :: L)
    [] (by cases b <;> rfl) (by
      intro a ha; rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> rfl)
  have h4 := rewind 4 3 .blank .separator
    ((w.map Symbol.ofBool).reverse ++ .zero :: ones j ++ .zero :: ones i) L
    ((v ++ [b]).map Symbol.ofBool) rfl (by
      intro a ha
      simp only [List.append_assoc] at ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases bit_mem (List.mem_reverse.mp ha) with rfl | rfl <;> rfl
      · rcases List.mem_cons.mp ha with ha | ha
        · subst a; rfl
        · rcases List.mem_append.mp ha with ha | ha
          · have := ones_mem ha; subst a; rfl
          · rcases List.mem_cons.mp ha with ha | ha
            · subst a; rfl
            · have := ones_mem ha; subst a; rfl)
  have h5 : Rch (cfg 2 (.zero :: ones i ++ .one :: L)
      (ones j ++ .zero :: w.map Symbol.ofBool ++ .separator :: (v ++ [b]).map Symbol.ofBool))
      (j + 1) (cfg 36 (.zero :: ones j ++ .zero :: ones i ++ .one :: L)
        (w.map Symbol.ofBool ++ .separator :: (v ++ [b]).map Symbol.ofBool)) := by
    have h := walkR 2 (ones j) (.zero :: ones i ++ .one :: L)
      (.zero :: w.map Symbol.ofBool ++ .separator :: (v ++ [b]).map Symbol.ofBool)
      (by intro a ha; have := ones_mem ha; subst a; rfl)
    simpa only [List.append_eq, Nat.zero_add, ones, List.length_replicate, List.reverse_replicate, List.cons_append,
      List.append_assoc] using trans h (R1 (a := .zero) rfl (Reaches.refl _))
  have h6 := walkR 1 (ones i) (.one :: L)
    (.zero :: ones j ++ .zero :: w.map Symbol.ofBool ++ .separator :: (v ++ [b]).map Symbol.ofBool)
    (by intro a ha; have := ones_mem ha; subst a; rfl)
  simp only [ones, List.length_replicate, List.reverse_replicate, List.map_append, List.map_cons,
    List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_reverse, List.length_reverse, List.length_map,
    List.length_append, List.length_cons, List.cons_append, List.append_assoc, List.singleton_append] at h1 h2 h3 h4 h5 h6 ⊢
  have h7 := trans h6 (R1 (q := 1) (a := .zero) rfl h5)
  have h8 := R1 (q := 3) (a := .blank) (w := .one) rfl h7
  have h9 := trans h4 h8
  have h10 := trans h3 h9
  have h11 : Rch (cfg (appendEnd b)
      ((v.map Symbol.ofBool).reverse ++ .separator :: (w.map Symbol.ofBool).reverse ++
        .zero :: List.replicate j .one ++ .zero :: List.replicate i .one ++ .blank :: L) T)
      (v.length + 1 + ((w.length + (j + (i + 1) + 1) + 1) + ((i + (j + 1 + 1)) + 1)))
      (cfg 36 (.zero :: List.replicate j .one ++ .zero :: List.replicate i .one ++ .one :: L)
        (w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ [Symbol.ofBool b])) := by
    rcases hT with rfl | rfl <;> simpa only [List.cons_append, List.append_assoc, cfg] using h10
  simp only [List.cons_append, List.append_assoc] at h11
  have h12 := trans h2 h11
  have h13 := R1 (q := appendSep b) (a := .separator) (by cases b <;> rfl) h12
  have h := trans h1 h13
  have ht : w.length + (v.length + (v.length + 1 +
      ((w.length + (j + (i + 1) + 1) + 1) + ((i + (j + 1 + 1)) + 1))) + 1) =
      2 * w.length + 2 * v.length + 2 * i + 2 * j + 8 := by omega
  rw [ht] at h
  exact h


theorem finish_padded (b : Bool) (w : Word) (L T : List Symbol)
    (hT : T = [] ∨ T = [.blank]) :
    Run candidate (cfg (if b then 29 else 28) L
      (w.map Symbol.ofBool ++ T)) (w.length + 1) (lastFrom b w) := by
  induction w generalizing b L with
  | nil => apply Run.halt; rcases hT with rfl | rfl <;> cases b <;> rfl
  | cons a w ih =>
      have hs : candidate.instruction (if b then 29 else 28)
          (Symbol.ofBool a) =
          .move (if a then 29 else 28) (Symbol.ofBool a) .right := by
        cases b <;> cases a <;> rfl
      exact Run.next (stepR hs _ _) (ih a (Symbol.ofBool a :: L))

theorem gate_empty_padded (v : Word) (L T : List Symbol) (hT : T = [] ∨ T = [.blank]) :
    Run candidate (cfg 36 L (.zero :: .separator :: v.map Symbol.ofBool ++ T))
      (v.length + 3) (v.getLastD false) := by
  have h := finish_padded false v (.separator :: .zero :: L) T hT
  rw [lastFrom_eq_getLastD] at h
  have h' := Run.next (stepR (q := 27) (a := .separator) rfl _ _) h
  have h'' := Run.next (stepR (q := 36) (a := .zero) rfl _ _) h'
  simpa only [List.cons_append, Nat.add_assoc] using h''

def secondKind (b : Bool) : LookupKind := if b then .secondTrue else .secondFalse

/-- A valid gate reads both wires, appends their NAND, and restores the tape. -/
theorem encNat_cells (n : Nat) : (encNat n).map Symbol.ofBool = ones n ++ [.zero] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [encNat, Symbol.ofBool, ones, List.replicate_succ] using congrArg (Symbol.one :: ·) ih

theorem gate_step (i j K : Nat) (w v : Word) (L T : List Symbol)
    (hi : i < v.length) (hj : j < v.length) (hT : T = [] ∨ T = [.blank])
    (hK : i + j + w.length + v.length + 10 ≤ K) :
    ∃ t, t ≤ 256 * K * K ∧
      Rch (cfg 36 L (.one :: ones i ++ .zero :: ones j ++ .zero ::
        w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T)) t
        (cfg 36 (.zero :: ones j ++ .zero :: ones i ++ .one :: L)
          (w.map Symbol.ofBool ++ .separator :: (v ++ [!(wire v i && wire v j)]).map Symbol.ofBool)) := by
  let r := encNat j ++ w
  have hr : r.map Symbol.ofBool = ones j ++ .zero :: w.map Symbol.ofBool := by
    simp only [r, List.map_append, encNat_cells, List.singleton_append, List.append_assoc]
  obtain ⟨t1, ht1, h1⟩ := lookup_success .first 0 i K r v L T hi (by
    simp only [r, List.length_append, length_encNat, lookupPrefix, List.length_nil] at *; omega)
  obtain ⟨t2, ht2, h2⟩ := lookup_success (secondKind (wire v i)) i j K w v L T hj (by
    have hp : (lookupPrefix (secondKind (wire v i)) i).length = i + 1 := by
      unfold secondKind; cases wire v i <;> simp [lookupPrefix, ones]
    rw [hp]; omega)
  have hp : (lookupPrefix (secondKind (wire v i)) i).reverse = .zero :: ones i := by
    unfold secondKind; cases wire v i <;> simp [lookupPrefix, ones]
  have hq : lookupInit (secondKind (wire v i)) = lookupExit .first (wire v i) := by
    unfold secondKind; cases wire v i <;> rfl
  have he : lookupExit (secondKind (wire v i)) (wire v j) = appendSep (!(wire v i && wire v j)) := by
    unfold secondKind; cases wire v i <;> cases wire v j <;> rfl
  have h3 := append_gate (!(wire v i && wire v j)) i j w v L T hT
  simp only [hr, lookupPrefix, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_assoc] at h1
  simp only [hp, hq, he, List.cons_append, List.append_assoc] at h2
  simp only [List.cons_append, List.append_assoc] at h3
  have h := trans h1 (trans h2 h3)
  have h' := R1 (q := 36) (a := .one) (w := .blank) rfl h
  simp only [List.cons_append, List.append_assoc] at h' ⊢
  refine ⟨t1 + (t2 + (2 * w.length + 2 * v.length + 2 * i + 2 * j + 8)) + 1, ?_, h'⟩
  have hiK : i + 1 ≤ K := by omega
  have hjK : j + 1 ≤ K := by omega
  have hk : 1 ≤ K := by omega
  have ha : 2 * w.length + 2 * v.length + 2 * i + 2 * j + 9 ≤ 64 * K := by omega
  have h1b := Nat.le_trans ht1 (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 64 hiK))
  have h2b := Nat.le_trans ht2 (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 64 hjK))
  have hab : _ ≤ 64 * K * K := Nat.le_trans ha (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (64 * K) hk)
  have heq : 64 * K * K + (64 * K * K + 64 * K * K) ≤ 256 * K * K := by
    simp only [Nat.mul_assoc]; omega
  simp only [Nat.mul_assoc] at h1b h2b hab heq ⊢
  omega


theorem gate_reject (i j K : Nat) (w v : Word) (L T : List Symbol)
    (hb : ¬(i < v.length ∧ j < v.length)) (hT : T = [] ∨ T = [.blank])
    (hK : i + j + w.length + v.length + 10 ≤ K) :
    ∃ t, t ≤ 256 * K * K ∧
      Run candidate (cfg 36 L (.one :: ones i ++ .zero :: ones j ++ .zero ::
        w.map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T)) t false := by
  let r := encNat j ++ w
  have hr : r.map Symbol.ofBool = ones j ++ .zero :: w.map Symbol.ofBool := by
    simp only [r, List.map_append, encNat_cells, List.singleton_append, List.append_assoc]
  have hK1 : i + r.length + v.length + (lookupPrefix .first 0).length + 4 ≤ K := by
    simp only [r, List.length_append, length_encNat, lookupPrefix, List.length_nil]; omega
  have hiK : i + 1 ≤ K := by omega
  have hjK : j + 1 ≤ K := by omega
  have hk : 1 ≤ K := by omega
  have hbudget : 64 * K * K + 64 * K * K + 1 ≤ 256 * K * K := by
    have hk2 : 1 ≤ K * K := Nat.le_trans hk (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right K hk)
    simp only [Nat.mul_assoc]; omega
  by_cases hi : i < v.length
  · have hj : v.length ≤ j := by omega
    obtain ⟨t1, ht1, h1⟩ := lookup_success .first 0 i K r v L T hi hK1
    obtain ⟨t2, ht2, h2⟩ := lookup_reject (secondKind (wire v i)) i j K w v L T hj hT (by
      have hp : (lookupPrefix (secondKind (wire v i)) i).length = i + 1 := by
        unfold secondKind; cases wire v i <;> simp [lookupPrefix, ones]
      rw [hp]; omega)
    have hp : (lookupPrefix (secondKind (wire v i)) i).reverse = .zero :: ones i := by
      unfold secondKind; cases wire v i <;> simp [lookupPrefix, ones]
    have hq : lookupInit (secondKind (wire v i)) = lookupExit .first (wire v i) := by
      unfold secondKind; cases wire v i <;> rfl
    simp only [hr, lookupPrefix, List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc] at h1
    simp only [hp, hq, List.cons_append, List.append_assoc] at h2
    have h := Run.next (stepR (q := 36) (a := .one) (w := .blank) rfl _ _) (h1.run h2)
    refine ⟨t1 + t2 + 1, ?_, ?_⟩
    · have h1b := Nat.le_trans ht1 (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 64 hiK))
      have h2b := Nat.le_trans ht2 (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 64 hjK))
      simp only [Nat.mul_assoc] at h1b h2b hbudget ⊢
      omega
    · simpa only [List.cons_append, List.append_assoc] using h
  · obtain ⟨t, ht, h⟩ := lookup_reject .first 0 i K r v L T (by omega) hT hK1
    simp only [hr, lookupPrefix, List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc] at h
    refine ⟨t + 1, ?_, ?_⟩
    · have ht' := Nat.le_trans ht (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 64 hiK))
      simp only [Nat.mul_assoc] at ht' hbudget ⊢
      omega
    · simpa only [List.cons_append, List.append_assoc] using
        Run.next (stepR (q := 36) (a := .one) (w := .blank) rfl _ _) h


/-- The gate loop evaluates every topological circuit and rejects a forward
wire. Its polynomial bound counts every lookup, append, and final halt. -/
theorem gate_loop (C : Circuit) : ∀ (v : Word) (L T : List Symbol) (K : Nat),
    (T = [] ∨ T = [.blank]) →
    (encList encGate C).length + v.length + 10 ≤ K →
    ∃ t, t ≤ 512 * (C.length + 1) * K * K ∧
      Run candidate (cfg 36 L
        ((encList encGate C).map Symbol.ofBool ++ .separator :: v.map Symbol.ofBool ++ T)) t
        (wfFromb v.length C && output v C) := by
  induction C with
  | nil =>
      intro v L T K hT hK
      refine ⟨v.length + 3, ?_, ?_⟩
      · have hk : 1 ≤ K := by omega
        have hv : v.length + 3 ≤ 512 * K := by omega
        have hb : 512 * K ≤ 512 * K * K := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (512 * K) hk
        simpa only [List.length_nil, Nat.zero_add, Nat.mul_one] using Nat.le_trans hv hb
      · simpa only [encList, List.map_cons, List.map_nil, Symbol.ofBool, List.singleton_append,
          wfFromb, Bool.true_and, output, wires] using gate_empty_padded v L T hT
  | cons g C ih =>
      rcases g with ⟨i,j⟩
      intro v L T K hT hK
      have hlen : (encList encGate ((i,j) :: C)).length = i + j + 3 + (encList encGate C).length := by
        simp only [encList, encGate, List.length_cons, List.length_append, length_encNat]; omega
      have hK' : i + j + (encList encGate C).length + v.length + 10 ≤ K := by rw [hlen] at hK; omega
      have henc : (encList encGate ((i,j) :: C)).map Symbol.ofBool =
          .one :: ones i ++ .zero :: ones j ++ .zero :: (encList encGate C).map Symbol.ofBool := by
        simp only [encList, encGate, List.map_cons, List.map_append, Symbol.ofBool, encNat_cells,
          List.singleton_append, List.cons_append, List.append_assoc, List.nil_append]
      by_cases hg : i < v.length ∧ j < v.length
      · obtain ⟨t1, ht1, h1⟩ := gate_step i j K (encList encGate C) v L T hg.1 hg.2 hT hK'
        obtain ⟨t2, ht2, h2⟩ := ih (v ++ [!(wire v i && wire v j)])
          (.zero :: ones j ++ .zero :: ones i ++ .one :: L) [] K (Or.inl rfl) (by
            simp only [List.length_append, List.length_cons, List.length_nil]; rw [hlen] at hK; omega)
        refine ⟨t1 + t2, ?_, ?_⟩
        · have hb : 256 * K * K + 512 * (C.length + 1) * K * K ≤
              512 * (C.length + 2) * K * K := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; omega
          simpa only [List.length_cons, Nat.add_assoc] using Nat.le_trans (Nat.add_le_add ht1 ht2) hb
        · simp only [List.append_nil, List.cons_append, List.append_assoc] at h2
          simp only [List.cons_append, List.append_assoc] at h1
          have h := h1.run h2
          simpa only [henc, List.cons_append, List.append_assoc, wfFromb, decide_eq_true hg.1,
            decide_eq_true hg.2, Bool.true_and, List.length_append, List.length_cons,
            List.length_nil, output, wires] using h
      · obtain ⟨t, ht, hr⟩ := gate_reject i j K (encList encGate C) v L T hg hT hK'
        refine ⟨t, ?_, ?_⟩
        · have hb : 256 * K * K ≤ 512 * (C.length + 2) * K * K := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; omega
          simpa only [List.length_cons, Nat.add_assoc] using Nat.le_trans ht hb
        · have hf : wfFromb v.length ((i,j) :: C) = false := by
            by_cases hi : i < v.length
            · have hj : ¬ j < v.length := fun hj => hg ⟨hi, hj⟩
              simp [wfFromb, hi, hj]
            · simp [wfFromb, hi]
          simpa only [henc, List.cons_append, List.append_assoc, hf, Bool.false_and] using hr


theorem whole_budget (a b c K : Nat) (hk : 1 ≤ K)
    (ha : a ≤ 4 * K) (hb : b ≤ 64 * K * K) (hc : c ≤ 512 * K * K * K) :
    a + (b + c) ≤ 1024 * K ^ 3 := by
  have hkk : 1 ≤ K * K := Nat.le_trans hk (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right K hk)
  have ha' : a ≤ 4 * K * (K * K) := Nat.le_trans ha (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * K) hkk)
  have hb' : b ≤ 64 * K * K * K := Nat.le_trans hb (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (64 * K * K) hk)
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at ha' hb' hc ⊢
  omega

/-- Every input/certificate pair has a correct, charged, polynomially bounded
run of this one finite table. No certificate or syntax premise is assumed. -/
theorem verifier_run (x cert : Word) :
    ∃ t, t ≤ 1024 * (x.length + cert.length + 12)^3 ∧
      Run candidate (pairedInput x cert) t (verifyCircuit x cert) := by
  let K := x.length + cert.length + 12
  have hk : 1 ≤ K := by simp only [K]; omega
  have hs : 2 * x.length + 2 ≤ 4 * K := by simp only [K]; omega
  cases hd : decCircuit x with
  | none =>
      have hbad : Issue567.CircuitSyntax.circuitSyntax x = false := by
        cases hsx : Issue567.CircuitSyntax.circuitSyntax x with
        | false => rfl
        | true =>
            obtain ⟨n,C,h⟩ := (Issue567.CircuitSyntax.circuitSyntax_iff_decCircuit x).mp hsx
            rw [hd] at h; contradiction
      refine ⟨x.length + 1, ?_, ?_⟩
      · have hb := whole_budget (x.length + 1) 0 0 K hk (by omega) (Nat.zero_le _) (Nat.zero_le _)
        simpa only [Nat.add_zero] using hb
      · simpa only [verifyCircuit, hd] using malformed_reject x cert hbad
  | some parsed =>
      rcases parsed with ⟨n,C⟩
      have hx := decCircuit_sound hd
      have hstart := valid_start x cert ((Issue567.CircuitSyntax.circuitSyntax_iff_decCircuit x).mpr ⟨n,C,hd⟩)
      have henc : x.map Symbol.ofBool = ones n ++ .zero :: (encList encGate C).map Symbol.ofBool := by
        rw [hx]; simp only [encCircuit, List.map_append, encNat_cells, List.singleton_append,
          List.append_assoc, List.nil_append]
      have hlen : x.length = n + 1 + (encList encGate C).length := by
        rw [hx]; simp only [encCircuit, List.length_append, length_encNat]
      have hn : n + 1 ≤ K := by simp only [K]; omega
      have hcsize : n + (encList encGate C).length + cert.length + 4 ≤ K := by simp only [K]; omega
      have hgK : (encList encGate C).length + cert.length + 10 ≤ K := by simp only [K]; omega
      have hglen : C.length + 1 ≤ K := by
        have h := (decCircuit_data_bounds hd).2
        simp only [K]; omega
      simp only [henc, List.cons_append, List.append_assoc] at hstart
      by_cases hc : cert.length = n
      · obtain ⟨t1, ht1, h1⟩ := count_success n (encList encGate C) cert hc
        obtain ⟨t2, ht2, h2⟩ := gate_loop C cert (.zero :: ones n ++ [.blank]) [.blank] K (Or.inr rfl) hgK
        have hb : t1 ≤ 64 * K * K := Nat.le_trans ht1
          (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hn) hcsize)
        have hc' : t2 ≤ 512 * K * K * K := Nat.le_trans ht2
          (Nat.mul_le_mul_right K (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 512 hglen)))
        refine ⟨2 * x.length + 2 + (t1 + t2), whole_budget _ _ _ K hk hs hb hc', ?_⟩
        simp only [List.cons_append, List.append_assoc] at h1 h2
        have h := hstart.run (h1.run h2)
        simpa only [verifyCircuit, hd, hc, decide_true, Bool.and_true] using h
      · obtain ⟨t1, ht1, h1⟩ := count_reject n (encList encGate C) cert hc
        have hb : t1 ≤ 64 * K * K := Nat.le_trans ht1
          (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hn) hcsize)
        refine ⟨2 * x.length + 2 + t1, ?_, ?_⟩
        · simpa only [Nat.add_zero] using whole_budget _ _ 0 K hk hs hb (Nat.zero_le _)
        · simp only [List.cons_append, List.append_assoc] at h1
          simpa only [verifyCircuit, hd, decide_eq_false hc, Bool.and_false, Bool.false_and] using hstart.run h1


/-- Every halting run has the specified answer and the same cubic bound. -/
theorem verifier_correct {x cert : Word} {t : Nat} {b : Bool}
    (hr : Run candidate (pairedInput x cert) t b) :
    t ≤ 1024 * (x.length + cert.length + 12)^3 ∧ b = verifyCircuit x cert := by
  obtain ⟨u, hu, hr'⟩ := verifier_run x cert
  obtain ⟨ht, hb⟩ := run_deterministic hr hr'
  exact ⟨ht ▸ hu, hb⟩

/-- Acceptance by the finite table agrees exactly with the certificate check. -/
theorem verifier_accepts (x cert : Word) :
    (∃ t, Run candidate (pairedInput x cert) t true) ↔ verifyCircuit x cert = true := by
  constructor
  · rintro ⟨t, hr⟩
    exact (verifier_correct hr).2.symm
  · intro h
    obtain ⟨t, _, hr⟩ := verifier_run x cert
    exact ⟨t, h ▸ hr⟩

end Issue532.CircuitVerifier
