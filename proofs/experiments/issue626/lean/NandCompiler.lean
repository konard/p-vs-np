import proofs.experiments.issue532.lean.CircuitModel

/-! Input-wire expressions compiled to the shared NAND straight-line model.
Constants are made from an actual input wire, so positive input length is
essential. Compilation never receives an input word or a language predicate. -/

namespace Issue626.NandCompiler

open Complexity Issue532.Circuits

inductive Expr where
  | input (index : Nat)
  | lit (value : Bool)
  | nand (a b : Expr)
  deriving Repr

def Expr.eval (x : List Bool) : Expr → Bool
  | .input i => wire x i
  | .lit b => b
  | .nand a b => !(a.eval x && b.eval x)

def Expr.Bounded (n : Nat) : Expr → Prop
  | .input i => i < n
  | .lit _ => True
  | .nand a b => a.Bounded n ∧ b.Bounded n

/-- Exact gate charge of this compiler, including constant generation. -/
def Expr.cost : Expr → Nat
  | .input _ => 0
  | .lit true => 2
  | .lit false => 3
  | .nand a b => a.cost + b.cost + 1

/-- Return gates and the wire holding the result. Intermediate results are
referenced by wire number; they are not recursively re-evaluated at runtime. -/
def compile (n : Nat) : Expr → Circuit × Nat
  | .input i => ([], i)
  | .lit true => ([(0, 0), (0, n)], n + 1)
  | .lit false => ([(0, 0), (0, n), (n + 1, n + 1)], n + 2)
  | .nand a b =>
      let (A, i) := compile n a
      let (B, j) := compile (n + A.length) b
      (A ++ B ++ [(i, j)], n + A.length + B.length)

theorem wires_append (x : List Bool) (A B : Circuit) :
    wires x (A ++ B) = wires (wires x A) B := by
  induction A generalizing x with
  | nil => rfl
  | cons g A ih => cases g; exact ih _

theorem wires_length (x : List Bool) (C : Circuit) :
    (wires x C).length = x.length + C.length := by
  induction C generalizing x with
  | nil => simp [wires]
  | cons g C ih => cases g; simp [wires, ih]; omega

/-- Every gate preserves every earlier wire, including the original inputs. -/
theorem wires_preserve (x : List Bool) (C : Circuit) (i : Nat)
    (hi : i < x.length) : wire (wires x C) i = wire x i := by
  induction C generalizing x with
  | nil => rfl
  | cons g C ih =>
      cases g with
      | mk a b =>
          rw [wires, ih _ (by simp; omega), wire_append_lt _ _ _ hi]

theorem WFfrom_append (n : Nat) (A B : Circuit) :
    WFfrom n (A ++ B) ↔ WFfrom n A ∧ WFfrom (n + A.length) B := by
  induction A generalizing n with
  | nil => simp [WFfrom]
  | cons g A ih =>
      cases g
      simp only [List.cons_append, WFfrom, List.length_cons, ih]
      have : n + 1 + A.length = n + (A.length + 1) := by omega
      rw [this]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem Expr.bounded_mono {a : Expr} {n k : Nat} (h : a.Bounded n)
    (hn : n ≤ k) : a.Bounded k := by
  induction a with
  | input i => exact Nat.lt_of_lt_of_le h hn
  | lit b => trivial
  | nand a b ia ib => exact ⟨ia h.1, ib h.2⟩

theorem Expr.eval_preserve {a : Expr} (x : List Bool) (C : Circuit)
    (h : a.Bounded x.length) : a.eval (wires x C) = a.eval x := by
  induction a with
  | input i => exact wires_preserve x C i h
  | lit b => rfl
  | nand a b ia ib => simp only [Expr.eval, ia h.1, ib h.2]

theorem compile_cost (n : Nat) (a : Expr) : (compile n a).1.length = a.cost := by
  induction a generalizing n with
  | input i => rfl
  | lit b => cases b <;> rfl
  | nand a b ia ib => simp [compile, Expr.cost, ia, ib, Nat.add_assoc]

theorem compile_WF (n : Nat) (a : Expr) (hn : 0 < n) (ha : a.Bounded n) :
    WFfrom n (compile n a).1 ∧ (compile n a).2 < n + (compile n a).1.length := by
  induction a generalizing n with
  | input i => exact ⟨trivial, ha⟩
  | lit b => cases b <;> simp [compile, WFfrom] <;> omega
  | nand a b ia ib =>
      obtain ⟨hwa, hi⟩ := ia n hn ha.1
      obtain ⟨hwb, hj⟩ := ib (n + (compile n a).1.length) (by omega)
        (Expr.bounded_mono ha.2 (by omega))
      simp only [compile]
      constructor
      · rw [WFfrom_append, WFfrom_append]
        refine ⟨⟨hwa, hwb⟩, ?_⟩
        simp only [List.length_append, WFfrom]
        exact ⟨by omega, by omega, trivial⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega

theorem compile_correct (x : List Bool) (a : Expr) (hx : 0 < x.length)
    (ha : a.Bounded x.length) :
    wire (wires x (compile x.length a).1) (compile x.length a).2 = a.eval x := by
  induction a generalizing x with
  | input i => rfl
  | lit b =>
      cases b
      · simp only [compile, wires, Expr.eval]
        rw [show x.length + 2 =
          ((x ++ [!(wire x 0 && wire x 0)]) ++
          [!(wire (x ++ [!(wire x 0 && wire x 0)]) 0 &&
             wire (x ++ [!(wire x 0 && wire x 0)]) x.length)]).length by simp]
        rw [wire_append_self]
        rw [show x.length + 1 = (x ++ [!(wire x 0 && wire x 0)]).length by simp]
        rw [wire_append_self, wire_append_lt _ _ _ hx, wire_append_self]
        cases wire x 0 <;> rfl
      · simp only [compile, wires, Expr.eval]
        rw [show x.length + 1 = (x ++ [!(wire x 0 && wire x 0)]).length by simp]
        rw [wire_append_self, wire_append_lt _ _ _ hx, wire_append_self]
        cases wire x 0 <;> rfl
  | nand a b ia ib =>
      let A := (compile x.length a).1
      let y := wires x A
      have hy : y.length = x.length + A.length := wires_length x A
      have hy0 : 0 < y.length := by omega
      have hb : b.Bounded y.length := Expr.bounded_mono ha.2 (by omega)
      have eb := ib y hy0 hb
      have ea := ia x hx ha.1
      have ep := b.eval_preserve x A ha.2
      simp only [compile, wires_append, wires, Expr.eval]
      rw [← hy]
      rw [show y.length + (compile y.length b).1.length =
          (wires y (compile y.length b).1).length from (wires_length _ _).symm]
      rw [wire_append_self]
      rw [wires_preserve y _ _ (by
        obtain ⟨_, hi⟩ := compile_WF x.length a hx ha.1
        simpa [hy, A] using hi)]
      rw [ea, eb, ep]

def Expr.neg (a : Expr) : Expr := .nand a a
def Expr.conj (a b : Expr) : Expr := (Expr.nand a b).neg
def Expr.disj (a b : Expr) : Expr := .nand a.neg b.neg
def Expr.mux (s a b : Expr) : Expr := .nand (.nand s a) (.nand s.neg b)

@[simp] theorem eval_mux (x : List Bool) (s a b : Expr) :
    (s.mux a b).eval x = if s.eval x then a.eval x else b.eval x := by
  simp only [Expr.mux, Expr.neg, Expr.eval]
  cases s.eval x <;> cases a.eval x <;> cases b.eval x <;> rfl

/-- Compile several outputs, preserving references to earlier results. -/
def compileMany (n : Nat) : List Expr → Circuit × List Nat
  | [] => ([], [])
  | a :: rest =>
      let (A, i) := compile n a
      let (B, js) := compileMany (n + A.length) rest
      (A ++ B, i :: js)

def totalCost (es : List Expr) : Nat := (es.map Expr.cost).sum

theorem compileMany_cost (n : Nat) (es : List Expr) :
    (compileMany n es).1.length = totalCost es := by
  induction es generalizing n with
  | nil => rfl
  | cons a es ih => simp [compileMany, totalCost, compile_cost, ih]

theorem compileMany_WF (n : Nat) (es : List Expr) (hn : 0 < n)
    (he : ∀ a ∈ es, a.Bounded n) :
    WFfrom n (compileMany n es).1 ∧
    ∀ i ∈ (compileMany n es).2, i < n + (compileMany n es).1.length := by
  induction es generalizing n with
  | nil => simp [compileMany, WFfrom]
  | cons a es ih =>
      have ha := he a (by simp)
      obtain ⟨hwa, hi⟩ := compile_WF n a hn ha
      obtain ⟨hwb, hjs⟩ := ih (n + (compile n a).1.length) (by omega)
        (fun b hb => Expr.bounded_mono (he b (by simp [hb])) (by omega))
      simp only [compileMany, List.length_append, List.mem_cons]
      refine ⟨(WFfrom_append _ _ _).mpr ⟨hwa, hwb⟩, ?_⟩
      intro j hj
      rcases hj with rfl | hj
      · omega
      · have := hjs j hj; omega

theorem compileMany_correct (x : List Bool) (es : List Expr) (hx : 0 < x.length)
    (he : ∀ a ∈ es, a.Bounded x.length) :
    (compileMany x.length es).2.map (wire (wires x (compileMany x.length es).1)) =
      es.map (Expr.eval x) := by
  induction es generalizing x with
  | nil => rfl
  | cons a es ih =>
      let A := (compile x.length a).1
      let y := wires x A
      have hy : y.length = x.length + A.length := wires_length x A
      have ha := he a (by simp)
      have hs := ih y (by omega)
        (fun b hb => Expr.bounded_mono (he b (by simp [hb])) (by omega))
      simp only [compileMany, List.map_cons, wires_append]
      rw [← hy]
      simp only [List.cons.injEq]
      constructor
      · rw [wires_preserve y _ _ (by
            obtain ⟨_, hi⟩ := compile_WF x.length a hx ha
            simpa [hy, A] using hi)]
        exact compile_correct x a hx ha
      · rw [hs]
        apply List.map_congr_left
        intro b hb
        exact b.eval_preserve x A (he b (by simp [hb]))

theorem compileMany_outputs_length (n : Nat) (es : List Expr) :
    (compileMany n es).2.length = es.length := by
  induction es generalizing n with
  | nil => rfl
  | cons a es ih => simp only [compileMany, List.length_cons, ih]

end Issue626.NandCompiler
