import proofs.experiments.issue624.lean.InitialCNF

/-! Generated schema syntax and data. Regenerate with
`python3 experiments/issue624/generate_schema.py`. The arithmetic product is
needed for row index * variable stride; literal ranges encode long clauses.
No second CNF evaluator or trace semantics is introduced. -/
namespace Issue624.Schema
open Complexity Issue532.Machines Issue624.LocalCNF Issue624.MachineCNF
open Issue624.SuccessorCNF Issue624.RunCNF Issue624.InitialCNF
open Issue624.CertificateCNF Issue624.VerifierTableau Issue624.FixedWindow

inductive Expr where
  | const (value : Nat) | param (slot : Nat) | idx (slot : Nat)
  | bit (position : Expr)
  | add (a b : Expr) | mul (a b : Expr) | sub (a b : Expr)
  | selectEq (a b yes no : Expr)
  deriving Repr, DecidableEq

def setIndex (indices : Nat → Nat) (slot value : Nat) : Nat → Nat :=
  fun k => if k = slot then value else indices k

def evalExpr (e : Expr) (params : List Nat) (x : Word) (indices : Nat → Nat) : Nat :=
  match e with
  | .const n => n | .param k => (params[k]?).getD 0 | .idx k => indices k
  | .bit e => if (x[evalExpr e params x indices]?).getD false then 1 else 0
  | .add a b => evalExpr a params x indices + evalExpr b params x indices
  | .mul a b => evalExpr a params x indices * evalExpr b params x indices
  | .sub a b => evalExpr a params x indices - evalExpr b params x indices
  | .selectEq a b yes no => if evalExpr a params x indices = evalExpr b params x indices
      then evalExpr yes params x indices else evalExpr no params x indices

inductive Literals where
  | list (values : List (Expr × Bool))
  | append (a b : Literals)
  | range (slot : Nat) (count value : Expr) (pos : Bool)
  deriving Repr, DecidableEq

def evalLiterals (ls : Literals) (params : List Nat) (x : Word) (indices : Nat → Nat) : Clause :=
  match ls with
  | .list vs => vs.map fun (e, p) => ⟨evalExpr e params x indices, p⟩
  | .append a b => evalLiterals a params x indices ++ evalLiterals b params x indices
  | .range slot count value pos => (List.range (evalExpr count params x indices)).map
      fun i => ⟨evalExpr value params x (setIndex indices slot i), pos⟩

inductive Schema where
  | empty | clause (values : Literals) | seq (a b : Schema)
  | forRange (slot : Nat) (count : Expr) (body : Schema)
  | ifLt (a b : Expr) (yes no : Schema)
  | guard (guards : Literals) (body : Schema)
  deriving Repr, DecidableEq

def evalSchema (s : Schema) (params : List Nat) (x : Word) (indices : Nat → Nat) : CNF :=
  match s with
  | .empty => [] | .clause vs => [evalLiterals vs params x indices]
  | .seq a b => evalSchema a params x indices ++ evalSchema b params x indices
  | .forRange slot count body => (List.range (evalExpr count params x indices)).flatMap
      fun i => evalSchema body params x (setIndex indices slot i)
  | .ifLt a b yes no => if evalExpr a params x indices < evalExpr b params x indices
      then evalSchema yes params x indices else evalSchema no params x indices
  | .guard guards body => (evalSchema body params x indices).map
      fun c => evalLiterals guards params x indices ++ c

def seqSchemas (ss : List Schema) : Schema := ss.foldr Schema.seq .empty

def oneHotSchema (d : Nat) (base : Expr) (size : Expr) : Schema :=
  (.seq (.clause (.range d size (.add base (.idx d)) true)) (.forRange d size (.forRange (d + 1) (.sub (.sub size (.idx d)) (.const 1)) (.clause (.list [((.add base (.idx d)), false), ((.add (.add base (.const 1)) (.add (.idx d) (.idx (d + 1)))), false)])))))

def certificateSchema (d : Nat) (start : Expr) (bound : Expr) : Schema :=
  (.seq (.forRange d bound (.seq (.clause (.list [((.add (.mul (.const 2) (.add start (.idx d))) (.const 1)), false), ((.mul (.const 2) (.add start (.idx d))), true)])) (.clause (.list [((.mul (.const 2) (.add (.add start (.idx d)) (.const 1))), false), ((.mul (.const 2) (.add start (.idx d))), true)])))) (.clause (.list [((.mul (.const 2) (.add start bound)), false)])))

def rowSchema (d : Nat) (base : Expr) (states : Expr) (width : Expr) : Schema :=
  (.seq (oneHotSchema d base states) (.seq (oneHotSchema d (.add base states) width) (.forRange d width (oneHotSchema (d + 1) (.add (.add (.add base states) width) (.mul (.const 4) (.idx d))) (.const 4)))))

def guardLiterals (base : Expr) (states : Expr) (width : Expr) (q : Nat) (head : Expr) (symbol : Nat) : Literals :=
  (.list [((.add base (.const q)), false), ((.add (.add base states) head), false), ((.add (.add (.add (.add base states) width) (.mul (.const 4) head)) (.const symbol)), false)])

def copySchema (d : Nat) (prem : Literals) (base : Expr) (next : Expr) (states : Expr) (width : Expr) (head : Expr) (write : Nat) : Schema :=
  (.forRange d width (.forRange (d + 1) (.const 4) (.guard prem (.clause (.list [((.add (.add (.add (.add base states) width) (.mul (.const 4) (.idx d))) (.idx (d + 1))), false), ((.add (.add (.add (.add next states) width) (.mul (.const 4) (.idx d))) (.selectEq (.idx d) head (.const write) (.idx (d + 1)))), true)])))))

def sourceSchema (base : Expr) (position : Expr) : Schema :=
  (.seq (.clause (.list [((.mul (.const 2) position), true), (base, true)])) (.seq (.clause (.list [((.mul (.const 2) position), false), ((.add (.mul (.const 2) position) (.const 1)), true), ((.add base (.const 1)), true)])) (.clause (.list [((.mul (.const 2) position), false), ((.add (.mul (.const 2) position) (.const 1)), false), ((.add base (.const 2)), true)]))))

def instructionSchema (d : Nat) (m : Machine) (base : Expr) (next : Expr) (width : Expr) (q : Nat) (head : Expr) (symbol : Nat) : Schema :=
  (match m.instruction q (symbolOfIndex symbol) with | .halt _ => (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.clause (.list []))) | .move target write dir => (if target < (m.program.length) then (match dir with | .left => (.ifLt (.const 0) head (.seq (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.seq (.clause (.list [((.add next (.const target)), true)])) (.clause (.list [((.add (.add next (.const (m.program.length))) (match dir with | .left => (.sub head (.const 1)) | .right => (.add head (.const 1)) | .stay => head)), true)])))) (copySchema d (guardLiterals base (.const (m.program.length)) width q head symbol) base next (.const (m.program.length)) width head (write.index))) (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.clause (.list [])))) | .right => (.ifLt (.add head (.const 1)) width (.seq (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.seq (.clause (.list [((.add next (.const target)), true)])) (.clause (.list [((.add (.add next (.const (m.program.length))) (match dir with | .left => (.sub head (.const 1)) | .right => (.add head (.const 1)) | .stay => head)), true)])))) (copySchema d (guardLiterals base (.const (m.program.length)) width q head symbol) base next (.const (m.program.length)) width head (write.index))) (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.clause (.list [])))) | .stay => (.seq (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.seq (.clause (.list [((.add next (.const target)), true)])) (.clause (.list [((.add (.add next (.const (m.program.length))) (match dir with | .left => (.sub head (.const 1)) | .right => (.add head (.const 1)) | .stay => head)), true)])))) (copySchema d (guardLiterals base (.const (m.program.length)) width q head symbol) base next (.const (m.program.length)) width head (write.index)))) else (.guard (guardLiterals base (.const (m.program.length)) width q head symbol) (.clause (.list [])))))

def transitionSchema (d : Nat) (m : Machine) (base : Expr) (next : Expr) (width : Expr) : Schema :=
  (seqSchemas ((List.range (m.program.length)).map fun q => (.forRange d width (seqSchemas ((List.range 4).map fun symbol => (instructionSchema (d + 1) m base next width q (.idx d) symbol))))))

def haltSchema (d : Nat) (m : Machine) (base : Expr) (width : Expr) : Schema :=
  (seqSchemas ((List.range (m.program.length)).map fun q => (.forRange d width (seqSchemas ((List.range 4).map fun symbol => (if m.instruction q (symbolOfIndex symbol) = .halt true then (.empty) else (.guard (guardLiterals base (.const (m.program.length)) width q (.idx d) symbol) (.clause (.list [])))))))))

def successorSchema (d : Nat) (m : Machine) (base : Expr) (next : Expr) (width : Expr) : Schema :=
  (.seq (rowSchema d base (.const (m.program.length)) width) (.seq (rowSchema d next (.const (m.program.length)) width) (transitionSchema d m base next width)))

def stopLiterals (d : Nat) (base : Expr) (states : Expr) (width : Expr) (count : Expr) : Literals :=
  (.range d count (.add (.add base (.mul (.add (.add states (.mul (.const 5) width)) (.const 1)) (.idx d))) (.add states (.mul (.const 5) width))) true)

def runSchema (d : Nat) (m : Machine) (base : Expr) (width : Expr) (fuel : Expr) : Schema :=
  (.seq (.forRange d fuel (.guard (stopLiterals (d + 1) base (.const (m.program.length)) width (.idx d)) (.seq (rowSchema (d + 1) (.add base (.mul (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1)) (.idx d))) (.const (m.program.length)) width) (.seq (.guard (.list [((.add (.add base (.mul (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1)) (.idx d))) (.add (.const (m.program.length)) (.mul (.const 5) width))), false)]) (haltSchema (d + 1) m (.add base (.mul (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1)) (.idx d))) width)) (.guard (.list [((.add (.add base (.mul (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1)) (.idx d))) (.add (.const (m.program.length)) (.mul (.const 5) width))), true)]) (successorSchema (d + 1) m (.add base (.mul (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1)) (.idx d))) (.add (.add base (.mul (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1)) (.idx d))) (.add (.add (.const (m.program.length)) (.mul (.const 5) width)) (.const 1))) width)))))) (.clause (stopLiterals d base (.const (m.program.length)) width fuel)))

def initialSchema (m : Machine) (paired : Bool) : Schema :=
  (.seq (rowSchema 0 (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length)) (.param 3)) (.seq (.clause (.list [((.add (.mul (.const 2) (.param 1)) (.const 1)), true)])) (.seq (.clause (.list [((.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 2)), true)])) (.seq (.forRange 0 (.param 2) (.clause (.list [((.add (.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 3)) (.mul (.const 4) (.add (.const 0) (.idx 0)))), true)]))) (.seq (.forRange 0 (.param 0) (.clause (.list [((.add (.add (.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 3)) (.mul (.const 4) (.add (.param 2) (.idx 0)))) (.add (.bit (.idx 0)) (.const 1))), true)]))) (if paired then (.seq (.clause (.list [((.add (.add (.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 3)) (.mul (.const 4) (.add (.param 2) (.param 0)))) (.const 3)), true)])) (.seq (.forRange 0 (.param 1) (sourceSchema (.add (.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 3)) (.mul (.const 4) (.add (.add (.add (.param 2) (.param 0)) (.const 1)) (.idx 0)))) (.idx 0))) (.forRange 0 (.sub (.sub (.sub (.sub (.param 3) (.param 2)) (.param 0)) (.const 1)) (.param 1)) (.clause (.list [((.add (.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 3)) (.mul (.const 4) (.add (.add (.add (.add (.param 2) (.param 0)) (.const 1)) (.param 1)) (.idx 0)))), true)]))))) else (.forRange 0 (.sub (.sub (.param 3) (.param 2)) (.param 0)) (.clause (.list [((.add (.add (.add (.add (.mul (.const 2) (.param 1)) (.const 1)) (.const (m.program.length))) (.param 3)) (.mul (.const 4) (.add (.add (.param 2) (.param 0)) (.idx 0)))), true)])))))))))

def machineSchema (m : Machine) (paired : Bool) : Schema :=
  (.seq (certificateSchema 0 (.const 0) (.param 1)) (.seq (initialSchema m paired) (runSchema 0 m (.add (.mul (.const 2) (.param 1)) (.const 1)) (.param 3) (.param 2))))

def tableauSchema (np : ClassNP) : Schema :=
  (match np.verifier with | .ignoreCertificate m => (machineSchema m false) | .paired m => (machineSchema m true))

def tableauParams (np : ClassNP) (n : Nat) : List Nat :=
  [n, np.certBound.eval n, maxClock np n, windowWidth np n]

-- END GENERATED SCHEMA DATA

def Expr.Closed (depth : Nat) : Expr → Prop
  | .const _ | .param _ => True
  | .idx k => k < depth
  | .bit e => e.Closed depth
  | .add a b | .mul a b | .sub a b => a.Closed depth ∧ b.Closed depth
  | .selectEq a b y n => a.Closed depth ∧ b.Closed depth ∧ y.Closed depth ∧ n.Closed depth

@[simp] theorem setIndex_same (env : Nat → Nat) (d i : Nat) : setIndex env d i d = i := by
  simp [setIndex]
@[simp] theorem setIndex_other (env : Nat → Nat) (d i k : Nat) (h : k ≠ d) :
    setIndex env d i k = env k := by simp [setIndex, h]

theorem closed_mono (e : Expr) {d k : Nat} (h : e.Closed d) (hd : d ≤ k) : e.Closed k := by
  induction e <;> simp_all [Expr.Closed] <;> omega

theorem evalExpr_setIndex (e : Expr) (p : List Nat) (x : Word) (env : Nat → Nat)
    (d i : Nat) (h : e.Closed d) :
    evalExpr e p x (setIndex env d i) = evalExpr e p x env := by
  induction e <;> simp_all [Expr.Closed, evalExpr, setIndex] <;> omega

theorem flatMap_range_succ {α : Type} (n : Nat) (f : Nat → List α) :
    (List.range (n + 1)).flatMap f = f 0 ++ (List.range n).flatMap (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map]
  simp [List.flatMap_map]

theorem map_range_succ {α : Type} (n : Nat) (f : Nat → α) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]

theorem flatMap_congr {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ a ∈ xs, f a = g a) : xs.flatMap f = xs.flatMap g := by
  simp only [List.flatMap_def]
  rw [List.map_congr_left h]

theorem atMostOne_range (base size : Nat) :
    atMostOne base size = (List.range size).flatMap fun i =>
      (List.range (size - i - 1)).map fun j => [⟨base + i, false⟩, ⟨base + 1 + (i + j), false⟩] := by
  induction size generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [flatMap_range_succ]
    simp only [atMostOne, ih, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_zero, Nat.zero_add]
    congr 1
    apply flatMap_congr
    intro i hi
    simp only [Nat.add_sub_add_right]
    apply List.map_congr_left
    intro j hj
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem oneHotSchema_eq (d : Nat) (base size : Expr) (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hs : size.Closed d) :
    evalSchema (oneHotSchema d base size) p x env =
      oneHot (evalExpr base p x env) (evalExpr size p x env) := by
  have hb' := closed_mono base hb (Nat.le_succ d)
  have hs' := closed_mono size hs (Nat.le_succ d)
  simp only [oneHotSchema, evalSchema, evalLiterals, evalExpr, setIndex_same,
    evalExpr_setIndex base p x env d _ hb, evalExpr_setIndex size p x env d _ hs,
    oneHot, atMostOne_range]
  apply congrArg (List.append _)
  apply flatMap_congr
  intro i hi
  rw [← List.map_eq_flatMap]
  apply List.map_congr_left
  intro j hj
  simp only [List.map_cons, List.map_nil, evalExpr,
    evalExpr_setIndex base p x (setIndex env d i) (d+1) j hb',
    evalExpr_setIndex base p x env d i hb, setIndex_same]
  simp [setIndex, Nat.add_assoc]

theorem certificateCNF_range (start bound : Nat) :
    certificateCNF start bound =
      (List.range bound).flatMap (fun i =>
        [[⟨2 * (start + i) + 1, false⟩, ⟨2 * (start + i), true⟩],
         [⟨2 * (start + i + 1), false⟩, ⟨2 * (start + i), true⟩]]) ++
      [[⟨2 * (start + bound), false⟩]] := by
  induction bound generalizing start with
  | zero => simp [certificateCNF]
  | succ n ih =>
    rw [flatMap_range_succ]
    simp only [certificateCNF, ih]
    simp [Nat.add_left_comm, Nat.add_comm]

theorem certificateSchema_eq (d : Nat) (start bound : Expr) (p : List Nat) (x : Word)
    (env : Nat → Nat) (hs : start.Closed d) (_hb : bound.Closed d) :
    evalSchema (certificateSchema d start bound) p x env =
      certificateCNF (evalExpr start p x env) (evalExpr bound p x env) := by
  simp only [certificateSchema, evalSchema, evalLiterals, evalExpr, List.map_cons,
    List.map_nil, evalExpr_setIndex start p x env d _ hs, setIndex_same, certificateCNF_range]
  simp [Nat.add_assoc]

@[simp] theorem evalSeqSchemas (ss : List Schema) (p : List Nat) (x : Word) (env : Nat → Nat) :
    evalSchema (seqSchemas ss) p x env = ss.flatMap (fun s => evalSchema s p x env) := by
  induction ss <;> simp_all [seqSchemas, evalSchema]

theorem rowSchema_eq (d : Nat) (base states width : Expr) (p : List Nat) (x : Word)
    (env : Nat → Nat) (hb : base.Closed d) (hs : states.Closed d) (hw : width.Closed d) :
    evalSchema (rowSchema d base states width) p x env =
      rowCNF (evalExpr base p x env) (evalExpr states p x env) (evalExpr width p x env) := by
  have hbs : (Expr.add base states).Closed d := ⟨hb, hs⟩
  have hcell : (Expr.add (Expr.add (Expr.add base states) width) (Expr.mul (.const 4) (.idx d))).Closed (d+1) := by
    simp [Expr.Closed, closed_mono base hb (Nat.le_succ d),
      closed_mono states hs (Nat.le_succ d), closed_mono width hw (Nat.le_succ d)]
  simp only [rowSchema, evalSchema, oneHotSchema_eq d base states p x env hb hs,
    oneHotSchema_eq d (.add base states) width p x env hbs hw,
    evalExpr, rowCNF, List.append_assoc]
  apply congrArg (List.append _)
  apply congrArg (List.append _)
  apply flatMap_congr
  intro i hi
  rw [oneHotSchema_eq (d+1) _ (.const 4) p x (setIndex env d i) hcell trivial]
  simp [evalExpr, evalExpr_setIndex, hb, hs, hw, setIndex_same, tapeBase]

def Literals.Closed (depth : Nat) : Literals → Prop
  | .list vs => ∀ v ∈ vs, v.1.Closed depth
  | .append a b => a.Closed depth ∧ b.Closed depth
  | .range _ _ _ _ => False

theorem literals_closed_mono (vs : Literals) {d k : Nat} (h : vs.Closed d) (hd : d ≤ k) :
    vs.Closed k := by
  induction vs with
  | list ls => intro v hv; exact closed_mono _ (h v hv) hd
  | append a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | range _ _ _ _ => exact h

theorem evalLiterals_setIndex (vs : Literals) (p : List Nat) (x : Word) (env : Nat → Nat)
    (d i : Nat) (h : vs.Closed d) :
    evalLiterals vs p x (setIndex env d i) = evalLiterals vs p x env := by
  induction vs with
  | list ls =>
    apply List.map_congr_left
    intro v hv
    simp [evalExpr_setIndex _ _ _ _ _ _ (h v hv)]
  | append a b ia ib => simp [evalLiterals, ia h.1, ib h.2]
  | range _ _ _ _ => exact False.elim h

theorem guardLiterals_eq (base states width : Expr) (q : Nat) (head : Expr) (symbol : Nat)
    (p : List Nat) (x : Word) (env : Nat → Nat) :
    evalLiterals (guardLiterals base states width q head symbol) p x env =
      (guard (evalExpr base p x env) (evalExpr states p x env)
        (evalExpr width p x env) q (evalExpr head p x env) symbol).map negate := by
  rfl

theorem guardLiterals_closed (base states width head : Expr) (q symbol d : Nat)
    (hb : base.Closed d) (hs : states.Closed d) (hw : width.Closed d) (hh : head.Closed d) :
    (guardLiterals base states width q head symbol).Closed d := by
  simp [guardLiterals, Literals.Closed, Expr.Closed, hb, hs, hw, hh]

theorem copySchema_eq (d : Nat) (prem : Literals) (base next states width head : Expr)
    (write : Nat) (p : List Nat) (x : Word) (env : Nat → Nat)
    (hp : prem.Closed d) (hb : base.Closed d) (hn : next.Closed d)
    (hs : states.Closed d) (hw : width.Closed d) (hh : head.Closed d) :
    evalSchema (copySchema d prem base next states width head write) p x env =
      (List.range (evalExpr width p x env)).flatMap fun i => (List.range 4).map fun s =>
        evalLiterals prem p x env ++
          [⟨tapeVar (evalExpr base p x env) (evalExpr states p x env)
              (evalExpr width p x env) i s, false⟩,
           ⟨tapeVar (evalExpr next p x env) (evalExpr states p x env)
              (evalExpr width p x env) i (if i = evalExpr head p x env then write else s), true⟩] := by
  simp only [copySchema, evalSchema, evalExpr, List.map_singleton]
  apply flatMap_congr
  intro i hi
  rw [← List.map_eq_flatMap]
  apply List.map_congr_left
  intro j hj
  have hd : d ≠ d+1 := by omega
  have hstable (e : Expr) (he : e.Closed d) :
      evalExpr e p x (setIndex (setIndex env d i) (d+1) j) = evalExpr e p x env := by
    rw [evalExpr_setIndex e _ _ _ _ _ (closed_mono e he (Nat.le_succ d)),
      evalExpr_setIndex e _ _ _ _ _ he]
  have hp' := literals_closed_mono prem hp (Nat.le_succ d)
  simp only [evalLiterals, List.map_cons, List.map_nil, evalExpr, setIndex_same,
    evalLiterals_setIndex prem _ _ _ _ _ hp', evalLiterals_setIndex prem _ _ _ _ _ hp,
    hstable base hb, hstable next hn, hstable states hs, hstable width hw, hstable head hh,
    setIndex_other _ _ _ _ hd]
  simp [tapeVar, tapeBase]

theorem sourceSchema_eq (base position : Expr) (p : List Nat) (x : Word) (env : Nat → Nat) :
    evalSchema (sourceSchema base position) p x env =
      sourceCNF (evalExpr base p x env) (.certificate (evalExpr position p x env)) := by
  simp [sourceSchema, sourceCNF, evalSchema, evalLiterals, evalExpr, implies, negate]

theorem copyGuardSchema_eq (d : Nat) (base next width head : Expr) (m : Machine)
    (q symbol : Nat) (write : Symbol) (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hn : next.Closed d) (hw : width.Closed d) (hh : head.Closed d) :
    evalSchema (copySchema d (guardLiterals base (.const m.program.length) width q head symbol)
      base next (.const m.program.length) width head write.index) p x env =
      copyRules (guard (evalExpr base p x env) m.program.length
        (evalExpr width p x env) q (evalExpr head p x env) symbol)
        (evalExpr base p x env) (evalExpr next p x env) m.program.length
        (evalExpr width p x env) (evalExpr head p x env) write := by
  rw [copySchema_eq d (guardLiterals base (.const m.program.length) width q head symbol) base next (.const m.program.length) width head write.index p x env
    (guardLiterals_closed base (.const m.program.length) width head q symbol d hb trivial hw hh) hb hn trivial hw hh]
  simp [guardLiterals_eq, copyRules, implies, List.map_append, negate, evalExpr]

theorem instructionSchema_eq (d : Nat) (m : Machine) (base next width : Expr) (q : Nat)
    (head : Expr) (symbol : Nat) (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hn : next.Closed d) (hw : width.Closed d) (hh : head.Closed d) :
    evalSchema (instructionSchema d m base next width q head symbol) p x env =
      instructionRules m (evalExpr base p x env) (evalExpr next p x env)
        (evalExpr width p x env) q (evalExpr head p x env) symbol := by
  cases hi : m.instruction q (symbolOfIndex symbol) with
  | halt b =>
    simp [instructionSchema, instructionRules, hi, evalSchema, evalLiterals,
      guardLiterals_eq, implies, evalExpr]
  | move target write dir =>
    have hc := copyGuardSchema_eq d base next width head m q symbol write p x env hb hn hw hh
    by_cases ht : target < m.program.length
    · cases dir <;>
        simp [instructionSchema, instructionRules, hi, ht, evalSchema, evalLiterals,
          evalExpr, guardLiterals_eq, Inside, nextHead, stateVar, headVar, implies, hc]
    · simp [instructionSchema, instructionRules, hi, ht, evalSchema, evalLiterals,
        guardLiterals_eq, implies, evalExpr]

theorem transitionSchema_eq (d : Nat) (m : Machine) (base next width : Expr)
    (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hn : next.Closed d) (hw : width.Closed d) :
    evalSchema (transitionSchema d m base next width) p x env =
      transitionCNF m (evalExpr base p x env) (evalExpr next p x env) (evalExpr width p x env) := by
  simp only [transitionSchema, evalSeqSchemas, List.flatMap_map, evalSchema,
    transitionCNF]
  apply flatMap_congr
  intro q hq
  apply flatMap_congr
  intro h hh
  apply flatMap_congr
  intro sym hs
  rw [instructionSchema_eq (d+1) _ _ _ _ _ _ _ _ _ _
    (closed_mono base hb (Nat.le_succ d)) (closed_mono next hn (Nat.le_succ d))
    (closed_mono width hw (Nat.le_succ d)) (by simp [Expr.Closed])]
  simp [evalExpr, evalExpr_setIndex, hb, hn, hw, setIndex_same]

theorem haltSchema_eq (d : Nat) (m : Machine) (base width : Expr)
    (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hw : width.Closed d) :
    evalSchema (haltSchema d m base width) p x env =
      haltCNF m (evalExpr base p x env) (evalExpr width p x env) := by
  simp only [haltSchema, evalSeqSchemas, List.flatMap_map, evalSchema,
    haltCNF]
  apply flatMap_congr
  intro q hq
  apply flatMap_congr
  intro h hh
  apply flatMap_congr
  intro sym hs
  by_cases hi : m.instruction q (symbolOfIndex sym) = .halt true <;>
    simp [hi, haltRule, evalSchema, evalLiterals, evalExpr, guardLiterals,
      evalExpr_setIndex, hb, hw, setIndex_same, SuccessorCNF.guard, implies, negate,
      stateVar, headVar, tapeVar, tapeBase]

theorem successorSchema_eq (d : Nat) (m : Machine) (base next width : Expr)
    (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hn : next.Closed d) (hw : width.Closed d) :
    evalSchema (successorSchema d m base next width) p x env =
      successorCNF m (evalExpr base p x env) (evalExpr next p x env) (evalExpr width p x env) := by
  simp only [successorSchema, evalSchema,
    rowSchema_eq d base (.const m.program.length) width p x env hb trivial hw,
    rowSchema_eq d next (.const m.program.length) width p x env hn trivial hw,
    transitionSchema_eq d m base next width p x env hb hn hw, evalExpr,
    successorCNF, List.append_assoc]

theorem implies_singleton (l : Lit) : implies [l] = fun c => negate l :: c := rfl

def runBlock (m : Machine) (base width : Nat) : CNF :=
  rowCNF base m.program.length width ++
    guarded ⟨stopVar base m.program.length width, true⟩ (haltCNF m base width) ++
    guarded ⟨stopVar base m.program.length width, false⟩
      (successorCNF m base (nextBase base m.program.length width) width)

def stopPrefix (m : Machine) (base width count : Nat) : Clause :=
  (List.range count).map fun i => ⟨stopVar (base + stride m.program.length width * i)
    m.program.length width, true⟩

@[simp] theorem stopPrefix_zero (m : Machine) (base width : Nat) : stopPrefix m base width 0 = [] := rfl

theorem stopPrefix_succ (m : Machine) (base width n : Nat) :
    stopPrefix m base width (n+1) =
      ⟨stopVar base m.program.length width, true⟩ ::
        stopPrefix m (nextBase base m.program.length width) width n := by
  unfold stopPrefix
  rw [map_range_succ]
  simp [stopVar, nextBase, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem runCNF_range (m : Machine) (base width fuel : Nat) :
    runCNF m base width fuel =
      (List.range fuel).flatMap (fun j => (runBlock m (base + stride m.program.length width * j) width).map
        (fun c => stopPrefix m base width j ++ c)) ++ [stopPrefix m base width fuel] := by
  induction fuel generalizing base with
  | zero => simp [runCNF, stopPrefix]
  | succ n ih =>
    rw [flatMap_range_succ, stopPrefix_succ]
    simp only [Nat.mul_zero, Nat.add_zero, stopPrefix_zero,
      List.nil_append, runBlock, runCNF, ih,
      guarded, implies, negate, Bool.not_false,
      List.map_append, List.map_flatMap, List.map_map,
      List.map_cons, List.append_assoc]
    have he (j : Nat) : base + stride m.program.length width * (j+1) =
        nextBase base m.program.length width + stride m.program.length width * j := by
      simp [nextBase, Nat.mul_add, Nat.add_assoc, Nat.add_comm]
    simp only [he, stopPrefix_succ, List.cons_append]
    simp [implies_singleton, negate, Function.comp_def]

theorem stopLiterals_eq (d : Nat) (base width count : Expr) (m : Machine)
    (p : List Nat) (x : Word) (env : Nat → Nat) (hb : base.Closed d) (hw : width.Closed d) :
    evalLiterals (stopLiterals d base (.const m.program.length) width count) p x env =
      stopPrefix m (evalExpr base p x env) (evalExpr width p x env) (evalExpr count p x env) := by
  simp [stopLiterals, evalLiterals, evalExpr, evalExpr_setIndex, hb, hw, setIndex_same,
    stopPrefix, stopVar, stride, Nat.add_assoc]

theorem runSchema_eq (d : Nat) (m : Machine) (base width fuel : Expr)
    (p : List Nat) (x : Word) (env : Nat → Nat)
    (hb : base.Closed d) (hw : width.Closed d) :
    evalSchema (runSchema d m base width fuel) p x env =
      runCNF m (evalExpr base p x env) (evalExpr width p x env) (evalExpr fuel p x env) := by
  have hb' := closed_mono base hb (Nat.le_succ d)
  have hw' := closed_mono width hw (Nat.le_succ d)
  let str : Expr := .add (.add (.const m.program.length) (.mul (.const 5) width)) (.const 1)
  let row : Expr := .add base (.mul str (.idx d))
  let next : Expr := .add row str
  have hstr : str.Closed (d+1) := by simp [str, Expr.Closed, hw']
  have hrow : row.Closed (d+1) := by simp [row, Expr.Closed, hb', hstr]
  have hnext : next.Closed (d+1) := ⟨hrow, hstr⟩
  simp only [runSchema, evalSchema]
  rw [stopLiterals_eq d base width fuel m p x env hb hw, runCNF_range]
  apply congrArg (fun cs => cs ++ [stopPrefix m (evalExpr base p x env)
    (evalExpr width p x env) (evalExpr fuel p x env)])
  apply flatMap_congr
  intro j hj
  change evalSchema (.guard (stopLiterals (d+1) base (.const m.program.length) width (.idx d))
    (.seq (rowSchema (d+1) row (.const m.program.length) width)
      (.seq (.guard (.list [(.add row (.add (.const m.program.length) (.mul (.const 5) width)), false)])
        (haltSchema (d+1) m row width))
        (.guard (.list [(.add row (.add (.const m.program.length) (.mul (.const 5) width)), true)])
          (successorSchema (d+1) m row next width))))) p x (setIndex env d j) = _
  simp only [evalSchema,
    rowSchema_eq (d+1) row (.const m.program.length) width p x (setIndex env d j) hrow trivial hw',
    haltSchema_eq (d+1) m row width p x (setIndex env d j) hrow hw',
    successorSchema_eq (d+1) m row next width p x (setIndex env d j) hrow hnext hw',
    stopLiterals_eq (d+1) base width (.idx d) m p x (setIndex env d j) hb' hw',
    evalLiterals, List.map_cons, List.map_nil, evalExpr, setIndex_same,
    evalExpr_setIndex base p x env d j hb, evalExpr_setIndex width p x env d j hw]
  simp [row, next, str, evalExpr, evalExpr_setIndex, hb, hw, setIndex_same, runBlock,
    guarded, implies_singleton, negate, stopVar, nextBase, stride, List.append_assoc, Nat.add_assoc]

theorem tapeCNF_append (base : Nat) (xs ys : List Source) :
    tapeCNF base (xs ++ ys) = tapeCNF base xs ++ tapeCNF (base + 4 * xs.length) ys := by
  induction xs generalizing base with
  | nil => simp [tapeCNF]
  | cons s xs ih =>
    simp [tapeCNF, ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem tapeCNF_map_range (base count : Nat) (f : Nat → Source) :
    tapeCNF base ((List.range count).map f) =
      (List.range count).flatMap fun i => sourceCNF (base + 4*i) (f i) := by
  induction count generalizing base f with
  | zero => rfl
  | succ n ih =>
    rw [map_range_succ, flatMap_range_succ]
    simp [tapeCNF, ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem tapeCNF_blank (base count : Nat) :
    tapeCNF base (List.replicate count (.fixed .blank)) =
      (List.range count).map fun i => [⟨base + 4*i, true⟩] := by
  have hr : List.replicate count (.fixed .blank) =
      (List.range count).map (fun _ => Source.fixed .blank) := by
    rw [List.map_const', List.length_range]
  rw [hr, tapeCNF_map_range]
  simp only [sourceCNF, Symbol.index, Nat.add_zero]
  rw [← List.map_eq_flatMap]

theorem tapeCNF_bits (base : Nat) (x : Word) :
    tapeCNF base (x.map fun b => Source.fixed (Symbol.ofBool b)) =
      (List.range x.length).map fun i =>
        [⟨base + 4*i + (1 + if (x[i]?).getD false then 1 else 0), true⟩] := by
  induction x generalizing base with
  | nil => rfl
  | cons b x ih =>
    rw [List.length_cons, map_range_succ]
    simp only [List.map_cons, tapeCNF, ih, List.getElem?_cons_zero, Option.getD_some,
      Nat.mul_zero, Nat.add_zero, List.getElem?_cons_succ]
    cases b <;>
      simp [sourceCNF, Symbol.ofBool, Symbol.index, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]

theorem certificateSources_range (start bound : Nat) :
    certificateSources start bound = (List.range bound).map fun i => Source.certificate (start+i) := by
  induction bound generalizing start with
  | zero => rfl
  | succ n ih => rw [map_range_succ]; simp [certificateSources, ih, Nat.add_left_comm, Nat.add_comm]

theorem tapeCNF_certificate (base start bound : Nat) :
    tapeCNF base (certificateSources start bound) =
      (List.range bound).flatMap fun i => sourceCNF (base+4*i) (.certificate (start+i)) := by
  rw [certificateSources_range, tapeCNF_map_range]

theorem initialSchema_eq (m : Machine) (pairedInput : Bool) (x : Word) (B T W : Nat)
    (env : Nat → Nat) (hroom : T + x.length + (if pairedInput then 1+B else 0) ≤ W) :
    evalSchema (initialSchema m pairedInput) [x.length, B, T, W] x env =
      initialCNF (2*B+1) m.program.length T
        (windowSources (if pairedInput then .paired m else .ignoreCertificate m) x B T W) := by
  have hw : (windowSources (if pairedInput then .paired m else .ignoreCertificate m) x B T W).length = W := by
    apply windowSources_length
    cases pairedInput <;> simp_all [inputSources] <;> omega
  have hr : evalSchema (rowSchema 0 (.add (.mul (.const 2) (.param 1)) (.const 1))
      (.const m.program.length) (.param 3)) [x.length,B,T,W] x env =
        rowCNF (2*B+1) m.program.length W := by
    rw [rowSchema_eq 0 _ _ _ _ _ _ (by trivial) (by trivial) (by trivial)]
    rfl
  cases pairedInput
  all_goals
    simp only [Bool.false_eq_true, eq_self, ite_false, ite_true] at hw ⊢
    simp only [initialCNF, hw]
    simp only [windowSources, inputSources, tapeCNF_append, List.length_replicate,
      List.length_map, List.length_append, List.length_singleton, certificateSources_length,
      tapeCNF_blank, tapeCNF_bits, tapeCNF_certificate]
    simp only [initialSchema, evalSchema, hr, evalLiterals, evalExpr,
      sourceCNF, tapeCNF, implies]
    simp only [← List.map_eq_flatMap]
    simp [evalSchema, evalLiterals, evalExpr, setIndex, sourceSchema_eq, sourceCNF, implies, negate,
      Symbol.index, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.sub_sub,
      List.append_assoc, ← List.map_eq_flatMap]

theorem machineSchema_eq (m : Machine) (pairedInput : Bool) (x : Word) (B T W : Nat)
    (env : Nat → Nat) (hroom : T + x.length + (if pairedInput then 1+B else 0) ≤ W) :
    evalSchema (machineSchema m pairedInput) [x.length, B, T, W] x env =
      certificateCNF 0 B ++
        initialCNF (2*B+1) m.program.length T
          (windowSources (if pairedInput then .paired m else .ignoreCertificate m) x B T W) ++
        runCNF m (2*B+1) W T := by
  have hc := certificateSchema_eq 0 (.const 0) (.param 1) [x.length,B,T,W] x env trivial trivial
  have hi := initialSchema_eq m pairedInput x B T W env hroom
  have hr := runSchema_eq 0 m (.add (.mul (.const 2) (.param 1)) (.const 1))
    (.param 3) (.param 2) [x.length,B,T,W] x env (by simp [Expr.Closed]) trivial
  simp only [machineSchema, evalSchema, hc, hi, hr, evalExpr]
  simp [List.append_assoc]

theorem tableauSchema_fragments (np : ClassNP) (x : Word) (env : Nat → Nat) :
    evalSchema (tableauSchema np) (tableauParams np x.length) x env =
      certificateCNF 0 (np.certBound.eval x.length) ++
        initialCNF (2 * np.certBound.eval x.length + 1)
          (verifierMachine np.verifier).program.length (maxClock np x.length)
          (windowSources np.verifier x (np.certBound.eval x.length)
            (maxClock np x.length) (windowWidth np x.length)) ++
        runCNF (verifierMachine np.verifier) (2 * np.certBound.eval x.length + 1)
          (windowWidth np x.length) (maxClock np x.length) := by
  cases hv : np.verifier with
  | ignoreCertificate m =>
    simpa [tableauSchema, tableauParams, hv, verifierMachine] using
      machineSchema_eq m false x (np.certBound.eval x.length) (maxClock np x.length)
        (windowWidth np x.length) env (by simp [windowWidth]; omega)
  | paired m =>
    simpa [tableauSchema, tableauParams, hv, verifierMachine] using
      machineSchema_eq m true x (np.certBound.eval x.length) (maxClock np x.length)
        (windowWidth np x.length) env (by simp [windowWidth]; omega)

end Issue624.Schema
