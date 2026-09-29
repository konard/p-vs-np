import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532: SAT is in NP on the shared machine model

This file proves `satInNP : Issue532.Machines.SATInNP`, that is
`Complexity.InNP Issue532.Machines.SAT`, by building an explicit verifier table
for the `paired` verifier format of `Complexity.ClassNP` and proving it correct
and polynomially bounded. No step of the argument is assumed.

## The certificate

A certificate is a bit vector `c₀ c₁ …`; variable `i` gets `cᵢ`, and variables
past the end of the certificate get `false` (this is `toAssign`). For a
satisfiable formula the certificate `prefixOf a |x|` works, because every
variable of `decode x` is `< |x|` (`varsBelow_decode`). So `certBound` is
`n + 1` and the verifier accepts `(x, c)` iff `evalCNF (toAssign c) (decode x)`.

## The tape and the codes

The word `x` is read in bit pairs exactly as `decodeAux` reads it: `11` is a
tick, `0p` a literal with polarity `p`, `10` a clause end, and an odd trailing
bit is dropped. During the run the formula region holds a list of `Code`s, two
cells each:

* `tick = 11`, `lit p = 0p`, `cend = 10` (live codes, as in the input);
* `dead = 0S` (a deleted tick or an already evaluated literal);
* `satEnd = 1S` (the end of a clause that is already satisfied).

No code starts with the separator `S` and none contains a blank, so a pair that
starts with `S` is the end of the formula region, and the blank left of the
formula marks the left end of the tape.

## The machine

1. Parity pass (`pEven`, `pOdd`, `pErase`): walk right over `x` in pairs; if
   `x` has odd length, overwrite the trailing bit by `S`.
2. Rounds. `seek` walks right over the `S` cells to the leftmost unread
   certificate bit `b`, overwrites it by `S` and `ret b` walks left to the
   blank at the left end. The sweep `sw b k s` then rewrites the formula
   pairwise (`roundAux`): the first live tick of every literal becomes `dead`
   (flag `k` records that this literal already lost a tick); a live literal
   with no live tick left has variable index `0` relative to this round, so it
   is evaluated with value `b`, becomes `dead`, and if it is true it sets the
   clause flag `s`; a live clause end with `s` set becomes `satEnd`. After the
   round every live literal refers to the next certificate bit with index `0`.
3. When `seek` meets the blank past the certificate, `retF` returns to the
   left end and the final pass `fin` evaluates every remaining live literal
   with value `false` (`finalAux`): it rejects at a live clause end whose clause
   has no true literal and accepts at the end of the formula region.

The abstract value `evalT a T k s` of a code list is the value of the formula
it denotes under `a`; `evalT_pairsOf` identifies it with
`evalCNF a (decodeAux w k cur)` on the input, `round_eval` shows that one round
shifts the assignment by one bit, and `finalAux_eq` handles the final pass.
The machine lemmas (`sweep`, `finalSweep`, `phase0`, `roundReaches`,
`finalRun`, `loopRun`) show that the table performs exactly these rewrites,
and `verifier_run` puts them together: the verifier halts on every pair
`(x, c)` within `5 (|x| + |c| + 2)²` steps with the answer
`evalCNF (toAssign c) (decode x)`.
-/

namespace Issue532.SATVerifier

open Complexity Issue532.Machines

/-! ## Codes on the tape -/

/-- A two-cell code of the formula region. -/
inductive Code where
  | tick
  | lit (p : Bool)
  | cend
  | dead
  | satEnd
  deriving DecidableEq, Repr

/-- The cells of one code. -/
def codeCells : Code → List Symbol
  | .tick => [.one, .one]
  | .lit p => [.zero, Symbol.ofBool p]
  | .cend => [.one, .zero]
  | .dead => [.zero, .separator]
  | .satEnd => [.one, .separator]

/-- The cells of a code list. -/
def tapeOf : List Code → List Symbol
  | [] => []
  | x :: T => codeCells x ++ tapeOf T

/-- The code of an input bit pair, as `decodeAux` reads it. -/
def pairCode : Bool → Bool → Code
  | true, true => .tick
  | true, false => .cend
  | false, p => .lit p

/-- The input read in bit pairs; an odd trailing bit is dropped. -/
def pairsOf : List Bool → List Code
  | a :: b :: r => pairCode a b :: pairsOf r
  | _ => []

/-! ## The abstract algorithm -/

/-- The value under `a` of the formula denoted by a code list. `k` counts the
live ticks of the current literal and `s` is the value of the current clause so
far. An unfinished clause at the end is dropped, as in `decodeAux`. -/
def evalT (a : Assignment) : List Code → Nat → Bool → Bool
  | [], _, _ => true
  | .tick :: r, k, s => evalT a r (k + 1) s
  | .lit p :: r, k, s => evalT a r 0 (s || (a k == p))
  | .cend :: r, _, s => s && evalT a r 0 false
  | .dead :: r, k, s => evalT a r k s
  | .satEnd :: r, _, _ => evalT a r 0 false

/-- One code of a sweep with certificate bit `b`: returns the rewritten code
and the new flags (`k`: this literal already lost a tick; `s`: the current
clause is already satisfied by a literal evaluated in this round). -/
def roundStep (b k s : Bool) : Code → Code × Bool × Bool
  | .tick => bif k then (.tick, true, s) else (.dead, true, s)
  | .lit p => bif k then (.lit p, false, s) else (.dead, false, s || (p == b))
  | .cend => (bif s then .satEnd else .cend, false, false)
  | .dead => (.dead, k, s)
  | .satEnd => (.satEnd, false, false)

/-- A sweep with certificate bit `b`. -/
def roundAux (b : Bool) : Bool → Bool → List Code → List Code
  | _, _, [] => []
  | k, s, x :: T =>
    (roundStep b k s x).1 :: roundAux b (roundStep b k s x).2.1 (roundStep b k s x).2.2 T

/-- All rounds, one per certificate bit, from the first bit on. -/
def rounds : List Bool → List Code → List Code
  | [], T => T
  | b :: c, T => rounds c (roundAux b false false T)

/-- The final pass: every remaining live literal is evaluated with value
`false`, so only negative live literals are true. -/
def finalAux : Bool → List Code → Bool
  | _, [] => true
  | s, .tick :: r => finalAux s r
  | s, .lit p :: r => finalAux (s || !p) r
  | s, .cend :: r => s && finalAux false r
  | s, .dead :: r => finalAux s r
  | _, .satEnd :: r => finalAux false r

/-! ## Correctness of the abstract algorithm -/

theorem evalClause_append (a : Assignment) (cur : Clause) (l : Lit) :
    evalClause a (cur ++ [l]) = (evalClause a cur || evalLit a l) := by
  induction cur with
  | nil => simp [evalClause]
  | cons l' c ih => simp [evalClause, ih, Bool.or_assoc]

/-- On the input, `evalT` is the value of the decoded formula. -/
theorem evalT_pairsOf (a : Assignment) :
    ∀ (w : List Bool) (k : Nat) (cur : Clause),
      evalT a (pairsOf w) k (evalClause a cur) = evalCNF a (decodeAux w k cur)
  | [], _, _ => by simp [pairsOf, decodeAux, evalT, evalCNF]
  | [x], _, _ => by cases x <;> simp [pairsOf, decodeAux, evalT, evalCNF]
  | true :: true :: r, k, cur => by
    simp only [pairsOf, pairCode, decodeAux, evalT]
    exact evalT_pairsOf a r (k + 1) cur
  | false :: p :: r, k, cur => by
    simp only [pairsOf, pairCode, decodeAux, evalT]
    have h := evalT_pairsOf a r 0 (cur ++ [⟨k, p⟩])
    rw [evalClause_append] at h
    exact h
  | true :: false :: r, k, cur => by
    simp only [pairsOf, pairCode, decodeAux, evalT, evalCNF]
    rw [← evalT_pairsOf a r 0 []]
    rfl

/-- One round with bit `b = a 0` turns the value under `a` into the value under
the shifted assignment `a'`. -/
theorem round_eval (a a' : Assignment) (b : Bool) (ha0 : a 0 = b)
    (has : ∀ i, a (i + 1) = a' i) :
    ∀ (T : List Code) (s' sn : Bool),
      (∀ k', evalT a' (roundAux b true s' T) k' sn = evalT a T (k' + 1) (sn || s')) ∧
        evalT a' (roundAux b false s' T) 0 sn = evalT a T 0 (sn || s') := by
  intro T
  induction T with
  | nil => intro s' sn; exact ⟨fun _ => rfl, rfl⟩
  | cons x T ih =>
    intro s' sn
    cases x with
    | tick =>
      refine ⟨fun k' => ?_, ?_⟩
      · simp only [roundAux, roundStep, Bool.cond_true, evalT]
        exact (ih s' sn).1 (k' + 1)
      · simp only [roundAux, roundStep, Bool.cond_false, evalT]
        exact (ih s' sn).1 0
    | lit p =>
      refine ⟨fun k' => ?_, ?_⟩
      · simp only [roundAux, roundStep, Bool.cond_true, evalT]
        rw [(ih s' _).2, has]
        cases sn <;> cases s' <;> simp
      · simp only [roundAux, roundStep, Bool.cond_false, evalT]
        rw [(ih _ sn).2, ha0]
        cases sn <;> cases s' <;> cases p <;> cases b <;> simp
    | cend =>
      refine ⟨fun k' => ?_, ?_⟩
      · cases s' <;> simp only [roundAux, roundStep, Bool.cond_true, Bool.cond_false, evalT] <;>
          rw [(ih false false).2] <;> simp
      · cases s' <;> simp only [roundAux, roundStep, Bool.cond_true, Bool.cond_false, evalT] <;>
          rw [(ih false false).2] <;> simp
    | dead =>
      refine ⟨fun k' => ?_, ?_⟩
      · simp only [roundAux, roundStep, evalT]
        exact (ih s' sn).1 k'
      · simp only [roundAux, roundStep, evalT]
        exact (ih s' sn).2
    | satEnd =>
      refine ⟨fun k' => ?_, ?_⟩
      · simp only [roundAux, roundStep, evalT]
        rw [(ih false false).2]; simp
      · simp only [roundAux, roundStep, evalT]
        rw [(ih false false).2]; simp

/-- The final pass is the value under the all-`false` assignment. -/
theorem finalAux_eq : ∀ (T : List Code) (k : Nat) (s : Bool),
    finalAux s T = evalT (fun _ => false) T k s := by
  intro T
  induction T with
  | nil => intro k s; rfl
  | cons x T ih =>
    intro k s
    cases x with
    | tick => exact ih _ _
    | lit p => simp only [finalAux, evalT]; rw [ih 0]; cases p <;> simp
    | cend => simp only [finalAux, evalT]; rw [ih 0]
    | dead => exact ih _ _
    | satEnd => simp only [finalAux, evalT]; rw [ih 0]

theorem toAssign_nil : toAssign [] = fun _ => false := by
  funext i; cases i <;> rfl

/-- The rounds followed by the final pass compute the value under the
certificate assignment. -/
theorem rounds_eval : ∀ (c : List Bool) (T : List Code),
    finalAux false (rounds c T) = evalT (toAssign c) T 0 false
  | [], T => by rw [rounds, finalAux_eq T 0, toAssign_nil]
  | b :: c, T => by
    rw [rounds, rounds_eval c]
    have h := (round_eval (toAssign (b :: c)) (toAssign c) b rfl (fun _ => rfl) T false false).2
    simpa using h

/-- The abstract verifier computes `evalCNF (toAssign c) (decode x)`. -/
theorem accept_value (x c : List Bool) :
    finalAux false (rounds c (pairsOf x)) = evalCNF (toAssign c) (decode x) := by
  rw [rounds_eval]
  exact evalT_pairsOf (toAssign c) x 0 []

/-! ## Variables of the decoded formula are below the input length -/

theorem varsBelow_decodeAux (n : Nat) :
    ∀ (w : List Bool) (k : Nat) (cur : Clause), k + w.length ≤ n →
      (∀ l ∈ cur, l.var < n) → VarsBelow n (decodeAux w k cur)
  | [], _, _, _, _ => by intro c hc; simp [decodeAux] at hc
  | [x], _, _, _, _ => by intro c hc; cases x <;> simp [decodeAux] at hc
  | true :: true :: r, k, cur, hk, hcur => by
    simp only [decodeAux]
    exact varsBelow_decodeAux n r (k + 1) cur (by simp at hk; omega) hcur
  | false :: p :: r, k, cur, hk, hcur => by
    simp only [decodeAux]
    refine varsBelow_decodeAux n r 0 (cur ++ [⟨k, p⟩]) (by simp at hk; omega) ?_
    intro l hl
    rcases List.mem_append.mp hl with h | h
    · exact hcur l h
    · simp at h; subst h; simp at hk; show k < n; omega
  | true :: false :: r, k, cur, hk, hcur => by
    simp only [decodeAux]
    intro c hc
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact hcur
    · exact varsBelow_decodeAux n r 0 [] (by simp at hk; omega) (by simp) c h

theorem varsBelow_decode (x : List Bool) : VarsBelow x.length (decode x) :=
  varsBelow_decodeAux x.length x 0 [] (by omega) (by simp)


/-! ## The machine -/

/-- Named machine states. -/
inductive St where
  | pEven | pOdd | pErase
  | seek
  | ret (b : Bool)
  | retF
  | fin (s : Bool) | fin0 (s : Bool) | fin1 (s : Bool)
  | sw (b k s : Bool) | sw0 (b k s : Bool) | sw1 (b k s : Bool)
  | back (b s : Bool) | fwd (b s : Bool)
  deriving DecidableEq, Repr

/-- Three flags as a number below `8`. -/
def bits3 (b k s : Bool) : Nat := 4 * b.toNat + 2 * k.toNat + s.toNat

/-- State numbers; `pEven` is the initial state `0`. -/
def idx : St → Nat
  | .pEven => 0
  | .pOdd => 1
  | .pErase => 2
  | .seek => 3
  | .ret b => 4 + b.toNat
  | .retF => 6
  | .fin s => 7 + s.toNat
  | .fin0 s => 9 + s.toNat
  | .fin1 s => 11 + s.toNat
  | .sw b k s => 13 + bits3 b k s
  | .sw0 b k s => 21 + bits3 b k s
  | .sw1 b k s => 29 + bits3 b k s
  | .back b s => 37 + 2 * b.toNat + s.toNat
  | .fwd b s => 41 + 2 * b.toNat + s.toNat

def triples : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

def pairs2 : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

/-- All states, listed in the order of `idx`. -/
def allStates : List St :=
  [.pEven, .pOdd, .pErase, .seek, .ret false, .ret true, .retF, .fin false, .fin true,
    .fin0 false, .fin0 true, .fin1 false, .fin1 true] ++
  triples.map (fun t => St.sw t.1 t.2.1 t.2.2) ++
  triples.map (fun t => St.sw0 t.1 t.2.1 t.2.2) ++
  triples.map (fun t => St.sw1 t.1 t.2.1 t.2.2) ++
  pairs2.map (fun t => St.back t.1 t.2) ++
  pairs2.map (fun t => St.fwd t.1 t.2)

theorem allStates_idx (q : St) : allStates[idx q]? = some q := by
  rcases q with _ | _ | _ | _ | b | _ | s | s | s | ⟨b, k, s⟩ | ⟨b, k, s⟩ | ⟨b, k, s⟩ |
    ⟨b, s⟩ | ⟨b, s⟩ <;>
  (try cases b) <;> (try cases k) <;> (try cases s) <;> rfl

def mv (q : St) (w : Symbol) (d : Direction) : Instruction := .move (idx q) w d

/-- The transition table, by state and scanned symbol. -/
def deltaSt : St → Symbol → Instruction
  -- parity pass
  | .pEven, .zero => mv .pOdd .zero .right
  | .pEven, .one => mv .pOdd .one .right
  | .pEven, .separator => mv .seek .separator .stay
  | .pOdd, .zero => mv .pEven .zero .right
  | .pOdd, .one => mv .pEven .one .right
  | .pOdd, .separator => mv .pErase .separator .left
  | .pErase, .zero => mv .seek .separator .stay
  | .pErase, .one => mv .seek .separator .stay
  -- find and erase the next certificate bit
  | .seek, .separator => mv .seek .separator .right
  | .seek, .zero => mv (.ret false) .separator .left
  | .seek, .one => mv (.ret true) .separator .left
  | .seek, .blank => mv .retF .blank .left
  -- return to the left end
  | .ret b, .blank => mv (.sw b false false) .blank .right
  | .ret b, .zero => mv (.ret b) .zero .left
  | .ret b, .one => mv (.ret b) .one .left
  | .ret b, .separator => mv (.ret b) .separator .left
  | .retF, .blank => mv (.fin false) .blank .right
  | .retF, .zero => mv .retF .zero .left
  | .retF, .one => mv .retF .one .left
  | .retF, .separator => mv .retF .separator .left
  -- final pass
  | .fin _, .separator => .halt true
  | .fin s, .zero => mv (.fin0 s) .zero .right
  | .fin s, .one => mv (.fin1 s) .one .right
  | .fin0 _, .zero => mv (.fin true) .zero .right
  | .fin0 s, .one => mv (.fin s) .one .right
  | .fin0 s, .separator => mv (.fin s) .separator .right
  | .fin1 s, .one => mv (.fin s) .one .right
  | .fin1 s, .zero => bif s then mv (.fin false) .zero .right else .halt false
  | .fin1 _, .separator => mv (.fin false) .separator .right
  -- one sweep with certificate bit `b`
  | .sw _ _ _, .separator => mv .seek .separator .stay
  | .sw b k s, .zero => mv (.sw0 b k s) .zero .right
  | .sw b k s, .one => mv (.sw1 b k s) .one .right
  | .sw0 b k s, .separator => mv (.sw b k s) .separator .right
  | .sw0 b k s, .zero =>
    bif k then mv (.sw b false s) .zero .right
    else mv (.sw b false (s || (false == b))) .separator .right
  | .sw0 b k s, .one =>
    bif k then mv (.sw b false s) .one .right
    else mv (.sw b false (s || (true == b))) .separator .right
  | .sw1 b k s, .one =>
    bif k then mv (.sw b true s) .one .right else mv (.back b s) .separator .left
  | .sw1 b _ s, .zero =>
    bif s then mv (.sw b false false) .separator .right
    else mv (.sw b false false) .zero .right
  | .sw1 b _ _, .separator => mv (.sw b false false) .separator .right
  | .back b s, .one => mv (.fwd b s) .zero .right
  | .fwd b s, .separator => mv (.sw b true s) .separator .right
  | _, _ => .halt false

/-- The row of a state, indexed by `Symbol.index`. -/
def row (q : St) : List Instruction :=
  [deltaSt q .blank, deltaSt q .zero, deltaSt q .one, deltaSt q .separator]

/-- The verifier table. -/
def verifier : Machine := ⟨allStates.map row⟩

theorem instr (q : St) (a : Symbol) : verifier.instruction (idx q) a = deltaSt q a := by
  unfold Machine.instruction verifier
  simp only [List.getElem?_map, allStates_idx, Option.map_some, Option.bind_some]
  cases a <;> rfl

/-! ## Configurations and single steps -/

/-- State `q`, reversed left part `L`, and the cells from the head on; an empty
cell list means a blank head at the right end. -/
def cfg (q : St) (L : List Symbol) : List Symbol → Config
  | [] => ⟨idx q, L, .blank, []⟩
  | a :: R => ⟨idx q, L, a, R⟩

theorem cfg_nil (q : St) (L : List Symbol) : cfg q L [] = cfg q L [.blank] := rfl

theorem stepR {q q' : St} {a w : Symbol} (h : deltaSt q a = mv q' w .right)
    (L R : List Symbol) : step verifier (cfg q L (a :: R)) = .inr (cfg q' (w :: L) R) := by
  unfold step
  simp only [cfg, instr, h, mv]
  cases R <;> rfl

theorem stepL {q q' : St} {a w : Symbol} (h : deltaSt q a = mv q' w .left)
    (l : Symbol) (L R : List Symbol) :
    step verifier (cfg q (l :: L) (a :: R)) = .inr (cfg q' L (l :: w :: R)) := by
  unfold step
  simp only [cfg, instr, h, mv]
  rfl

theorem stepL0 {q q' : St} {a w : Symbol} (h : deltaSt q a = mv q' w .left)
    (R : List Symbol) :
    step verifier (cfg q [] (a :: R)) = .inr (cfg q' [] (.blank :: w :: R)) := by
  unfold step
  simp only [cfg, instr, h, mv]
  rfl

theorem stepS {q q' : St} {a w : Symbol} (h : deltaSt q a = mv q' w .stay)
    (L R : List Symbol) : step verifier (cfg q L (a :: R)) = .inr (cfg q' L (w :: R)) := by
  unfold step
  simp only [cfg, instr, h, mv]
  rfl

theorem stepH {q : St} {a : Symbol} {b : Bool} (h : deltaSt q a = .halt b)
    (L R : List Symbol) : step verifier (cfg q L (a :: R)) = .inl b := by
  unfold step
  simp only [cfg, instr, h]

/-! ## Partial runs -/

abbrev Rch := Reaches verifier

theorem Reaches.trans' {m : Machine} {c d e : Config} {t u : Nat}
    (h : Reaches m c t d) (h' : Reaches m d u e) : Reaches m c (t + u) e := by
  induction h with
  | refl => simpa using h'
  | next hs _ ih => rw [Nat.add_right_comm]; exact Reaches.next hs (ih h')

theorem R1 {q q' : St} {a w : Symbol} {L R : List Symbol} {t : Nat} {E : Config}
    (h : deltaSt q a = mv q' w .right) (hr : Rch (cfg q' (w :: L) R) t E) :
    Rch (cfg q L (a :: R)) (t + 1) E :=
  Reaches.next (stepR h L R) hr

theorem L1 {q q' : St} {a w l : Symbol} {L R : List Symbol} {t : Nat} {E : Config}
    (h : deltaSt q a = mv q' w .left) (hr : Rch (cfg q' L (l :: w :: R)) t E) :
    Rch (cfg q (l :: L) (a :: R)) (t + 1) E :=
  Reaches.next (stepL h l L R) hr

theorem S1 {q q' : St} {a w : Symbol} {L R : List Symbol} {t : Nat} {E : Config}
    (h : deltaSt q a = mv q' w .stay) (hr : Rch (cfg q' L (w :: R)) t E) :
    Rch (cfg q L (a :: R)) (t + 1) E :=
  Reaches.next (stepS h L R) hr


/-! ## Sweeps -/

/-- One code of a sweep takes at most four steps (four for a deleted tick,
which needs one step back to rewrite the first cell). -/
theorem sweepCode (b k s : Bool) (x : Code) (L R : List Symbol) :
    ∃ t, t ≤ 4 ∧ Rch (cfg (.sw b k s) L (codeCells x ++ R)) t
      (cfg (.sw b (roundStep b k s x).2.1 (roundStep b k s x).2.2)
        ((codeCells (roundStep b k s x).1).reverse ++ L) R) := by
  cases x with
  | tick =>
    cases k
    · exact ⟨_, by decide, R1 rfl (L1 rfl (R1 rfl (R1 rfl (Reaches.refl _))))⟩
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
  | lit p =>
    cases k <;> cases p
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
  | cend =>
    cases s
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
    · exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
  | dead => exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩
  | satEnd => exact ⟨_, by decide, R1 rfl (R1 rfl (Reaches.refl _))⟩

theorem tapeOf_cons (x : Code) (T : List Code) : tapeOf (x :: T) = codeCells x ++ tapeOf T := rfl

/-- A whole sweep: the formula region is rewritten by `roundAux` and the
machine stops in `seek` on the separator that ends the region. -/
theorem sweep (b : Bool) : ∀ (T : List Code) (k s : Bool) (L R : List Symbol),
    ∃ t, t ≤ 4 * T.length + 1 ∧
      Rch (cfg (.sw b k s) L (tapeOf T ++ .separator :: R)) t
        (cfg .seek ((tapeOf (roundAux b k s T)).reverse ++ L) (.separator :: R))
  | [], k, s, L, R => ⟨1, by simp, S1 rfl (Reaches.refl _)⟩
  | x :: T, k, s, L, R => by
    obtain ⟨t1, ht1, h1⟩ := sweepCode b k s x L (tapeOf T ++ .separator :: R)
    obtain ⟨t2, ht2, h2⟩ := sweep b T (roundStep b k s x).2.1 (roundStep b k s x).2.2
      ((codeCells (roundStep b k s x).1).reverse ++ L) R
    refine ⟨t1 + t2, by simp; omega, ?_⟩
    rw [tapeOf_cons, List.append_assoc]
    have h := Reaches.trans' h1 h2
    simpa [roundAux, tapeOf_cons, List.reverse_append, List.append_assoc] using h

/-- The final pass accepts or rejects as `finalAux`. -/
theorem finalSweep : ∀ (T : List Code) (s : Bool) (L R : List Symbol),
    ∃ t, t ≤ 2 * T.length + 1 ∧
      Run verifier (cfg (.fin s) L (tapeOf T ++ .separator :: R)) t (finalAux s T)
  | [], s, L, R => ⟨1, by simp, Run.halt (stepH rfl L R)⟩
  | x :: T, s, L, R => by
    cases x with
    | tick =>
      obtain ⟨t, ht, h⟩ := finalSweep T s (.one :: .one :: L) R
      exact ⟨_, by simp; omega, (R1 rfl (R1 rfl (Reaches.refl _))).run h⟩
    | lit p =>
      cases p
      · obtain ⟨t, ht, h⟩ := finalSweep T true (.zero :: .zero :: L) R
        refine ⟨0 + 1 + 1 + t, by simp; omega, ?_⟩
        simp only [finalAux, Bool.not_false, Bool.or_true]
        exact Reaches.run (R1 rfl (R1 rfl (Reaches.refl _))) h
      · obtain ⟨t, ht, h⟩ := finalSweep T s (.one :: .zero :: L) R
        refine ⟨0 + 1 + 1 + t, by simp; omega, ?_⟩
        simp only [finalAux, Bool.not_true, Bool.or_false]
        exact Reaches.run (R1 rfl (R1 rfl (Reaches.refl _))) h
    | cend =>
      cases s
      · refine ⟨2, by simp; omega, ?_⟩
        exact Run.next (stepR rfl _ _) (Run.halt (stepH rfl _ _))
      · obtain ⟨t, ht, h⟩ := finalSweep T false (.zero :: .one :: L) R
        refine ⟨0 + 1 + 1 + t, by simp; omega, ?_⟩
        simp only [finalAux, Bool.true_and]
        exact Reaches.run (R1 rfl (R1 rfl (Reaches.refl _))) h
    | dead =>
      obtain ⟨t, ht, h⟩ := finalSweep T s (.separator :: .zero :: L) R
      exact ⟨_, by simp; omega, (R1 rfl (R1 rfl (Reaches.refl _))).run h⟩
    | satEnd =>
      obtain ⟨t, ht, h⟩ := finalSweep T false (.separator :: .one :: L) R
      exact ⟨_, by simp; omega, (R1 rfl (R1 rfl (Reaches.refl _))).run h⟩


/-! ## Walking over the tape -/

theorem walkR (q : St) : ∀ (w L R : List Symbol), (∀ a ∈ w, deltaSt q a = mv q a .right) →
    Rch (cfg q L (w ++ R)) w.length (cfg q (w.reverse ++ L) R)
  | [], L, R, _ => Reaches.refl _
  | a :: w, L, R, h => by
    have ih := walkR q w (a :: L) R (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    have h1 := R1 (L := L) (R := w ++ R) (h a (List.mem_cons_self ..)) ih
    simpa [Nat.add_comm] using h1

/-- Walking left to the blank at the left end. The part left of the formula is
either empty (first time) or the single blank cell created by the first walk. -/
theorem walkLEnd (q : St) (Lb : List Symbol) (hLb : Lb = [] ∨ Lb = [.blank]) :
    ∀ (w : List Symbol) (a : Symbol) (R : List Symbol),
      (∀ a' ∈ a :: w, deltaSt q a' = mv q a' .left) →
      Rch (cfg q (w ++ Lb) (a :: R)) (w.length + 1) (cfg q [] (.blank :: w.reverse ++ a :: R))
  | [], a, R, h => by
    have ha := h a (List.mem_cons_self ..)
    rcases hLb with rfl | rfl
    · exact Reaches.next (stepL0 ha R) (Reaches.refl _)
    · exact Reaches.next (stepL ha .blank [] R) (Reaches.refl _)
  | l :: w, a, R, h => by
    have ih := walkLEnd q Lb hLb w l (a :: R) (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    have h1 := L1 (L := w ++ Lb) (h a (List.mem_cons_self ..)) ih
    simpa [Nat.add_comm, Nat.add_left_comm] using h1

theorem ret_left (b : Bool) (a : Symbol) (ha : a ≠ .blank) :
    deltaSt (.ret b) a = mv (.ret b) a .left := by
  cases a
  · exact absurd rfl ha
  all_goals rfl

theorem retF_left (a : Symbol) (ha : a ≠ .blank) : deltaSt .retF a = mv .retF a .left := by
  cases a
  · exact absurd rfl ha
  all_goals rfl

theorem codeCells_ne_blank (x : Code) : ∀ a ∈ codeCells x, a ≠ .blank := by
  cases x with
  | lit p => cases p <;> decide
  | _ => decide

theorem tapeOf_ne_blank : ∀ (T : List Code), ∀ a ∈ tapeOf T, a ≠ .blank
  | [], _, h => by simp [tapeOf] at h
  | x :: T, a, h => by
    rw [tapeOf_cons] at h
    rcases List.mem_append.mp h with h | h
    · exact codeCells_ne_blank x a h
    · exact tapeOf_ne_blank T a h

theorem length_codeCells (x : Code) : (codeCells x).length = 2 := by
  cases x <;> rfl

theorem length_tapeOf : ∀ (T : List Code), (tapeOf T).length = 2 * T.length
  | [] => rfl
  | x :: T => by simp [tapeOf_cons, length_codeCells, length_tapeOf T]; omega

theorem length_roundAux (b : Bool) : ∀ (k s : Bool) (T : List Code),
    (roundAux b k s T).length = T.length
  | _, _, [] => rfl
  | k, s, x :: T => by simp [roundAux, length_roundAux b _ _ T]

theorem length_pairsOf : ∀ (x : List Bool), 2 * (pairsOf x).length ≤ x.length
  | [] => by simp [pairsOf]
  | [_] => by simp [pairsOf]
  | _ :: _ :: r => by simp [pairsOf]; have := length_pairsOf r; omega

theorem codeCells_pairCode (a b : Bool) :
    codeCells (pairCode a b) = [Symbol.ofBool a, Symbol.ofBool b] := by
  cases a <;> cases b <;> rfl

theorem replicate_cons_eq (n : Nat) (a : Symbol) (l : List Symbol) :
    List.replicate n a ++ a :: l = a :: (List.replicate n a ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-! ## The parity pass -/

theorem phase0 : ∀ (x : List Bool) (L R : List Symbol), ∃ t m, t ≤ x.length + 2 ∧ 1 ≤ m ∧
    m ≤ 2 ∧ Rch (cfg .pEven L (x.map Symbol.ofBool ++ .separator :: R)) t
      (cfg .seek ((tapeOf (pairsOf x)).reverse ++ L) (List.replicate m .separator ++ R))
  | [], L, R => ⟨1, 1, by simp, Nat.le_refl _, by decide, S1 rfl (Reaches.refl _)⟩
  | [a], L, R => by
    cases a
    · exact ⟨3, 2, by simp, by decide, by decide, R1 rfl (L1 rfl (S1 rfl (Reaches.refl _)))⟩
    · exact ⟨3, 2, by simp, by decide, by decide, R1 rfl (L1 rfl (S1 rfl (Reaches.refl _)))⟩
  | a :: b :: r, L, R => by
    obtain ⟨t, m, ht, hm1, hm2, h⟩ := phase0 r (Symbol.ofBool b :: Symbol.ofBool a :: L) R
    have e : (tapeOf (pairsOf (a :: b :: r))).reverse ++ L =
        (tapeOf (pairsOf r)).reverse ++ Symbol.ofBool b :: Symbol.ofBool a :: L := by
      simp [pairsOf, tapeOf_cons, codeCells_pairCode]
    refine ⟨t + 1 + 1, m, by simp; omega, hm1, hm2, ?_⟩
    rw [e]
    cases a <;> cases b <;> exact R1 rfl (R1 rfl h)


/-! ## Rounds and the final pass on the tape -/

abbrev seps (n : Nat) : List Symbol := List.replicate n .separator

theorem seps_right : ∀ a ∈ seps n, deltaSt .seek a = mv .seek a .right := by
  intro a ha
  rw [List.eq_of_mem_replicate ha]
  rfl

theorem seps_ne_blank {n : Nat} : ∀ a ∈ seps n, a ≠ .blank := by
  intro a ha
  rw [List.eq_of_mem_replicate ha]
  decide

theorem left_part_ne_blank (n : Nat) (T : List Code) :
    ∀ a ∈ .separator :: (seps n ++ (tapeOf T).reverse), a ≠ .blank := by
  intro a ha
  rcases List.mem_cons.mp ha with h | h
  · subst h; decide
  · rcases List.mem_append.mp h with h | h
    · exact seps_ne_blank a h
    · exact tapeOf_ne_blank T a (List.mem_reverse.mp h)

/-- One round: erase the next certificate bit `b`, return to the left end and
sweep the formula region with `b`. -/
theorem roundReaches (b : Bool) (c : List Bool) (T : List Code) (m : Nat)
    (Lb : List Symbol) (hLb : Lb = [] ∨ Lb = [.blank]) (hm : 1 ≤ m) :
    ∃ t, t ≤ 2 * m + 6 * T.length + 3 ∧
      Rch (cfg .seek ((tapeOf T).reverse ++ Lb) (seps m ++ Symbol.ofBool b :: c.map Symbol.ofBool))
        t (cfg .seek ((tapeOf (roundAux b false false T)).reverse ++ [.blank])
          (seps (m + 1) ++ c.map Symbol.ofBool)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 := walkR .seek (seps (m' + 1)) ((tapeOf T).reverse ++ Lb)
    (Symbol.ofBool b :: c.map Symbol.ofBool) seps_right
  rw [List.reverse_replicate, List.replicate_succ, List.cons_append] at h1
  have hb : deltaSt .seek (Symbol.ofBool b) = mv (.ret b) .separator .left := by
    cases b <;> rfl
  have h3 := walkLEnd (.ret b) Lb hLb (seps m' ++ (tapeOf T).reverse) .separator
    (.separator :: c.map Symbol.ofBool)
    (fun a ha => ret_left b a (left_part_ne_blank m' T a ha))
  rw [List.append_assoc] at h3
  have h2 := L1 hb h3
  have h4 := Reaches.trans' h1 h2
  obtain ⟨t5, ht5, h5⟩ := sweep b T false false [.blank] (seps (m' + 1) ++ c.map Symbol.ofBool)
  have h45 := R1 (L := []) (rfl : deltaSt (.ret b) .blank = mv (.sw b false false) .blank .right) h5
  have e : (seps m' ++ (tapeOf T).reverse).reverse ++ Symbol.separator :: Symbol.separator ::
      c.map Symbol.ofBool = tapeOf T ++ Symbol.separator :: (seps (m' + 1) ++ c.map Symbol.ofBool) := by
    simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_assoc]
    rw [replicate_cons_eq, replicate_cons_eq]
    rfl
  rw [← e] at h45
  have h := Reaches.trans' h4 h45
  refine ⟨_, ?_, h⟩
  simp [length_tapeOf]
  omega

/-- The certificate is used up: return to the left end and run the final pass. -/
theorem finalRun (T : List Code) (m : Nat) (Lb : List Symbol) (hLb : Lb = [] ∨ Lb = [.blank])
    (hm : 1 ≤ m) : ∃ t, t ≤ 2 * m + 4 * T.length + 3 ∧
      Run verifier (cfg .seek ((tapeOf T).reverse ++ Lb) (seps m)) t (finalAux false T) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 := walkR .seek (seps (m' + 1)) ((tapeOf T).reverse ++ Lb) [] seps_right
  rw [List.reverse_replicate, List.replicate_succ, List.cons_append, cfg_nil,
    List.append_nil] at h1
  have h3 := walkLEnd .retF Lb hLb (seps m' ++ (tapeOf T).reverse) .separator [.blank]
    (fun a ha => retF_left a (left_part_ne_blank m' T a ha))
  rw [List.append_assoc] at h3
  have h2 := L1 (rfl : deltaSt .seek .blank = mv .retF .blank .left) h3
  have h4 := Reaches.trans' h1 h2
  obtain ⟨t5, ht5, h5⟩ := finalSweep T false [.blank] (seps m' ++ [.blank])
  have h45 := Reaches.run
    (R1 (L := []) (rfl : deltaSt .retF .blank = mv (.fin false) .blank .right) (Reaches.refl _)) h5
  have e : (seps m' ++ (tapeOf T).reverse).reverse ++ [Symbol.separator, Symbol.blank] =
      tapeOf T ++ Symbol.separator :: (seps m' ++ [.blank]) := by
    simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_assoc]
    rw [← replicate_cons_eq]
  rw [← e] at h45
  have h := h4.run h45
  refine ⟨_, ?_, h⟩
  simp [length_tapeOf]
  omega

/-- All rounds and the final pass. -/
theorem loopRun : ∀ (c : List Bool) (T : List Code) (m : Nat) (Lb : List Symbol),
    (Lb = [] ∨ Lb = [.blank]) → 1 ≤ m →
    ∃ t, t ≤ (c.length + 1) * (2 * (m + c.length) + 6 * T.length + 4) ∧
      Run verifier (cfg .seek ((tapeOf T).reverse ++ Lb) (seps m ++ c.map Symbol.ofBool)) t
        (finalAux false (rounds c T))
  | [], T, m, Lb, hLb, hm => by
    obtain ⟨t, ht, h⟩ := finalRun T m Lb hLb hm
    refine ⟨t, by simp; omega, ?_⟩
    simpa [rounds] using h
  | b :: c, T, m, Lb, hLb, hm => by
    obtain ⟨t1, ht1, h1⟩ := roundReaches b c T m Lb hLb hm
    obtain ⟨t2, ht2, h2⟩ := loopRun c (roundAux b false false T) (m + 1) [.blank]
      (Or.inr rfl) (by omega)
    refine ⟨t1 + t2, ?_, h1.run h2⟩
    rw [length_roundAux] at ht2
    have e : 2 * (m + 1 + c.length) + 6 * T.length + 4 =
        2 * (m + (b :: c).length) + 6 * T.length + 4 := by simp; omega
    rw [e] at ht2
    simp only [List.length_cons] at ht2 ⊢
    rw [Nat.succ_mul (c.length + 1)]
    omega


/-! ## The whole run on a paired input -/

theorem initialSymbols_eq (l : List Symbol) : initialSymbols l = cfg .pEven [] l := by
  cases l <;> rfl

/-- On input `x # c` the verifier halts within `5 (|x| + |c| + 2)²` steps and
answers whether `toAssign c` satisfies `decode x`. -/
theorem verifier_run (x c : List Bool) : ∃ t, t ≤ 5 * (x.length + c.length + 1 + 1) ^ 2 ∧
    Run verifier (pairedInput x c) t (evalCNF (toAssign c) (decode x)) := by
  have e : pairedInput x c =
      cfg .pEven [] (x.map Symbol.ofBool ++ .separator :: c.map Symbol.ofBool) := by
    unfold pairedInput
    rw [initialSymbols_eq]
    simp
  obtain ⟨t1, m, ht1, hm1, hm2, h1⟩ := phase0 x [] (c.map Symbol.ofBool)
  obtain ⟨t2, ht2, h2⟩ := loopRun c (pairsOf x) m [] (Or.inl rfl) hm1
  rw [accept_value] at h2
  refine ⟨t1 + t2, ?_, by rw [e]; exact h1.run h2⟩
  have hp := length_pairsOf x
  have hA : (c.length + 1) * (2 * (m + c.length) + 6 * (pairsOf x).length + 4) ≤
      (x.length + c.length + 1 + 1) * (4 * (x.length + c.length + 1 + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hB := Nat.le_mul_self (x.length + c.length + 1 + 1)
  rw [Nat.mul_left_comm] at hA
  rw [Nat.pow_two]
  omega

/-! ## The NP record -/

/-- The verifier for SAT: `certBound = n + 1`, `timeBound = 5 (n + 1)²`. -/
def satNP : ClassNP where
  language := SAT
  verifier := .paired verifier
  timeBound := ⟨5, 2⟩
  certBound := ⟨1, 1⟩
  terminates := by
    intro x cert _
    obtain ⟨t, ht, h⟩ := verifier_run x cert
    exact ⟨t, _, ht, h⟩
  correct := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (sat_iff x).mp hx
      refine ⟨prefixOf a x.length, ?_⟩
      obtain ⟨t, ht, h⟩ := verifier_run x (prefixOf a x.length)
      have hv : evalCNF (toAssign (prefixOf a x.length)) (decode x) = true := by
        rw [evalCNF_congr (toAssign (prefixOf a x.length)) a x.length (decode x)
          (fun i hi => toAssign_prefixOf a x.length i hi) (varsBelow_decode x)]
        exact ha
      rw [hv] at h
      refine ⟨t, ?_, ht, h⟩
      show (prefixOf a x.length).length ≤ 1 * (x.length + 1) ^ 1
      rw [length_prefixOf, Nat.pow_one]
      omega
    · rintro ⟨cert, t, _, _, h⟩
      obtain ⟨t', _, h'⟩ := verifier_run x cert
      have hb := (run_deterministic h h').2
      exact (sat_iff x).mpr ⟨toAssign cert, hb.symm⟩

/-- SAT is in NP, on the shared machine model. -/
theorem satInNP : SATInNP := ⟨satNP, rfl⟩

/-- P = NP puts SAT in P (membership half of Cook–Levin now proved). -/
theorem inP_sat_of_pEqualsNP' (h : PEqualsNP) : InP SAT := inP_sat_of_pEqualsNP satInNP h

/-- Cook–Levin reduces to its hardness half. -/
theorem cookLevin_iff_satHard : CookLevin ↔ SATHard :=
  ⟨fun h => h.2, fun h => ⟨satInNP, h⟩⟩

/-- Given NP-hardness of SAT, SAT is in P exactly when P = NP. -/
theorem inP_sat_iff_of_hard (hard : SATHard) : InP SAT ↔ PEqualsNP :=
  inP_sat_iff ⟨satInNP, hard⟩


end Issue532.SATVerifier
