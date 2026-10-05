import proofs.experiments.issue532.lean.Circuits

/-!
# Issue #532, Idea 31: length-wise advice (truth-table circuits)

**Verdict: refuted as a route (general theorem).**

As a *non-uniform* tool the idea is correct and fully general: every Boolean
function on `n`-bit inputs is computed by the complete decision tree
`build n f` (a multiplexer / table lookup), for every `n`
(`build_correct`).  The tree has exactly `2 ^ n` leaves and `2 ^ (n + 1) - 1`
nodes (`build_leaves`, `build_size`); its leaves, read left to right, are the
truth table (`build_leafList`); the advice is exactly `2 ^ n` bits and
determines the function on length `n` (`advice_length`, `advice_injective`,
`ofTable_advice`).  No fixed advice length below `2 ^ n` works for all
functions (`no_shorter_advice`).

As a route to *uniform* algorithms it fails in general:

* the advice is exponential, and even parity (which is in P) needs a
  decision tree with `2 ^ n` leaves (`parity_tree_leaves`);
* advice can encode anything: every length-only ("unary") language has
  one-bit advice and one-node trees at every length (`unary_one_bit`), and for
  every enumeration of uniform deciders there is such a language that none of
  them decides (`advice_beyond_uniform`).

Machine model (shared `Machines`/`Circuits` layer).  `UniformAdvice L` asks
for advice `adv n` attached to the input by a polynomial-time
`Complexity.Machine` (so the advice is uniform and of polynomial length) and a
polynomial-time machine deciding `L` from the input with its advice.  The open
obligation is `UniformSATAdvice := UniformAdvice Machines.SAT`;
`inP_sat_of_uniformSATAdvice` and `pEqualsNP_of_uniformSATAdvice` derive
`InP SAT` and `PEqualsNP` from it, `not_uniformSATAdvice_of_superpoly` shows
that a superpolynomial circuit lower bound for SAT refutes it (using the
proved theorem `pSubsetPPoly`), `not_forall_uniformAdvice` is the non-vacuity
check, and `uniformPolyAdviceFor_of_uniformAdvice` instantiates the schema
`UniformPolyAdviceFor`.

Nothing here decides P vs NP.
-/

namespace Issue532.Idea31

/-- Binary decision trees: `node lo hi` reads the next input bit. -/
inductive DTree where
  | leaf : Bool → DTree
  | node : DTree → DTree → DTree

/-- Evaluation: bit `false` goes to `lo`, bit `true` goes to `hi`. -/
def DTree.eval : DTree → List Bool → Bool
  | .leaf b, _ => b
  | .node _ _, [] => false
  | .node lo hi, b :: x => if b then hi.eval x else lo.eval x

def DTree.leaves : DTree → Nat
  | .leaf _ => 1
  | .node lo hi => lo.leaves + hi.leaves

/-- Total number of nodes (leaves included). -/
def DTree.size : DTree → Nat
  | .leaf _ => 1
  | .node lo hi => lo.size + hi.size + 1

def DTree.leafList : DTree → List Bool
  | .leaf b => [b]
  | .node lo hi => lo.leafList ++ hi.leafList

/-- The complete decision tree (table lookup) of `f` on inputs of length `n`. -/
def build : Nat → (List Bool → Bool) → DTree
  | 0, f => .leaf (f [])
  | n + 1, f => .node (build n (fun x => f (false :: x))) (build n (fun x => f (true :: x)))

/-- The table-lookup tree is correct on every input of length `n`, for every `n`. -/
theorem build_correct (n : Nat) (f : List Bool → Bool) (x : List Bool)
    (h : x.length = n) : (build n f).eval x = f x := by
  induction n generalizing f x with
  | zero =>
    cases x with
    | nil => rfl
    | cons _ _ => simp at h
  | succ n ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      have hx : x.length = n := by simp at h; exact h
      cases b
      · simp only [build, DTree.eval]; exact ih _ x hx
      · simp only [build, DTree.eval]; exact ih _ x hx

/-- Exactly `2 ^ n` leaves. -/
theorem build_leaves (n : Nat) (f : List Bool → Bool) : (build n f).leaves = 2 ^ n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [build, DTree.leaves, ih, Nat.pow_succ]; omega

/-- Exactly `2 ^ (n + 1) - 1` nodes. -/
theorem build_size (n : Nat) (f : List Bool → Bool) : (build n f).size + 1 = 2 ^ (n + 1) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [build, DTree.size]
    have h1 := ih (fun x => f (false :: x))
    have h2 := ih (fun x => f (true :: x))
    rw [Nat.pow_succ]
    omega

/-- All inputs of length `n`, `false`-prefixed ones first. -/
def allBool : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBool n).map (fun w => false :: w) ++ (allBool n).map (fun w => true :: w)

theorem allBool_length (n : Nat) : (allBool n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allBool, ih, Nat.pow_succ]; omega

theorem mem_allBool (n : Nat) (x : List Bool) : x ∈ allBool n ↔ x.length = n := by
  induction n generalizing x with
  | zero => cases x <;> simp [allBool]
  | succ n ih =>
    simp only [allBool, List.mem_append, List.mem_map, ih]
    constructor
    · intro h
      cases h with
      | inl h => obtain ⟨w, hw, e⟩ := h; subst e; simp [hw]
      | inr h => obtain ⟨w, hw, e⟩ := h; subst e; simp [hw]
    · intro h
      cases x with
      | nil => simp at h
      | cons b w =>
        have hw : w.length = n := by simp at h; exact h
        cases b
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩

theorem nodup_map_cons (a : Bool) (W : List (List Bool)) (h : W.Nodup) :
    (W.map (fun w => a :: w)).Nodup := by
  induction W with
  | nil => exact List.nodup_nil
  | cons v W ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih h.2⟩
    intro ⟨u, hu, e⟩
    have : u = v := (List.cons.inj e).2
    subst this
    exact h.1 hu

theorem allBool_nodup (n : Nat) : (allBool n).Nodup := by
  induction n with
  | zero => simp [allBool]
  | succ n ih =>
    simp only [allBool]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons _ _ ih, nodup_map_cons _ _ ih, ?_⟩
    intro x hx y hy e
    obtain ⟨u, _, eu⟩ := List.mem_map.1 hx
    obtain ⟨v, _, ev⟩ := List.mem_map.1 hy
    subst eu; subst ev
    cases (List.cons.inj e).1

/-- The leaves of the table-lookup tree are the truth table of `f`. -/
theorem build_leafList (n : Nat) (f : List Bool → Bool) :
    (build n f).leafList = (allBool n).map f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [build, DTree.leafList, allBool, List.map_append, List.map_map, ih]
    rfl

/-- The advice string for length `n`: the truth table. -/
def advice (n : Nat) (f : List Bool → Bool) : List Bool := (build n f).leafList

/-- The advice is exactly `2 ^ n` bits. -/
theorem advice_length (n : Nat) (f : List Bool → Bool) : (advice n f).length = 2 ^ n := by
  rw [advice, build_leafList, List.length_map, allBool_length]

/-- Rebuild a tree from a table. -/
def ofTable : Nat → List Bool → DTree
  | 0, t => .leaf (t.headD false)
  | n + 1, t => .node (ofTable n (t.take (2 ^ n))) (ofTable n (t.drop (2 ^ n)))

/-- Decoding the advice recovers the table-lookup tree. -/
theorem ofTable_advice (n : Nat) (f : List Bool → Bool) :
    ofTable n (advice n f) = build n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have h1 := advice_length n (fun x => f (false :: x))
    simp only [advice, build, DTree.leafList] at h1 ⊢
    simp only [ofTable]
    rw [List.take_left' h1, List.drop_left' h1]
    have e1 := ih (fun x => f (false :: x))
    have e2 := ih (fun x => f (true :: x))
    simp only [advice] at e1 e2
    rw [e1, e2]

/-- The advice determines the function on inputs of length `n`. -/
theorem advice_injective (n : Nat) (f g : List Bool → Bool) (h : advice n f = advice n g) :
    ∀ x, x.length = n → f x = g x := by
  intro x hx
  rw [← build_correct n f x hx, ← build_correct n g x hx, ← ofTable_advice n f,
    ← ofTable_advice n g, h]

/-- Every table of length `2 ^ n` is realised: the table of `ofTable n t` is `t`. -/
theorem table_of_ofTable (n : Nat) (t : List Bool) (h : t.length = 2 ^ n) :
    (allBool n).map (ofTable n t).eval = t := by
  induction n generalizing t with
  | zero =>
    match t, h with
    | [b], _ => rfl
  | succ n ih =>
    have ht : (t.take (2 ^ n)).length = 2 ^ n := by
      rw [List.length_take, h, Nat.pow_succ]; omega
    have hd : (t.drop (2 ^ n)).length = 2 ^ n := by
      rw [List.length_drop, h, Nat.pow_succ]; omega
    simp only [allBool, List.map_append, List.map_map]
    have e1 : (allBool n).map ((ofTable (n + 1) t).eval ∘ fun w => false :: w)
        = t.take (2 ^ n) := by rw [← ih _ ht]; rfl
    have e2 : (allBool n).map ((ofTable (n + 1) t).eval ∘ fun w => true :: w)
        = t.drop (2 ^ n) := by rw [← ih _ hd]; rfl
    rw [e1, e2, List.take_append_drop]

/-- Pigeonhole: a duplicate-free list covered by the image of `codes` is no longer. -/
theorem cover_length {Code : Type} (decode : Code → List Bool)
    (targets : List (List Bool)) (codes : List Code) (hnd : targets.Nodup)
    (hcov : ∀ t, t ∈ targets → ∃ c, c ∈ codes ∧ decode c = t) :
    targets.length ≤ codes.length := by
  have hsub : targets ⊆ codes.map decode := by
    intro t ht
    obtain ⟨c, hc, e⟩ := hcov t ht
    exact List.mem_map.2 ⟨c, hc, e⟩
  have := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_map] at this
  exact this

/-- No advice scheme with fixed length `m < 2 ^ n` handles all functions on length `n`. -/
theorem no_shorter_advice (n m : Nat) (hm : m < 2 ^ n)
    (decode : List Bool → List Bool → Bool) :
    ∃ f : List Bool → Bool, ∀ a, a.length = m → ∃ x, x.length = n ∧ decode a x ≠ f x := by
  have hlt : (allBool m).length < (allBool (2 ^ n)).length := by
    rw [allBool_length, allBool_length]
    exact Nat.pow_lt_pow_right (by decide) hm
  have hunc : ∃ t, t ∈ allBool (2 ^ n) ∧
      ∀ a, a ∈ allBool m → (allBool n).map (decode a) ≠ t := by
    apply Classical.byContradiction
    intro hno
    have hcov : ∀ t, t ∈ allBool (2 ^ n) →
        ∃ a, a ∈ allBool m ∧ (allBool n).map (decode a) = t := by
      intro t ht
      apply Classical.byContradiction
      intro hc
      exact hno ⟨t, ht, fun a ha e => hc ⟨a, ha, e⟩⟩
    have := cover_length (fun a => (allBool n).map (decode a)) _ _ (allBool_nodup _) hcov
    omega
  obtain ⟨t, ht, hno⟩ := hunc
  have htl : t.length = 2 ^ n := (mem_allBool _ t).1 ht
  refine ⟨(ofTable n t).eval, ?_⟩
  intro a ha
  apply Classical.byContradiction
  intro hall
  apply hno a ((mem_allBool m a).2 ha)
  rw [← table_of_ofTable n t htl]
  apply List.map_congr_left
  intro x hx
  apply Classical.byContradiction
  intro hne
  exact hall ⟨x, (mem_allBool n x).1 hx, hne⟩

/-- Parity of a bit string. -/
def parity : List Bool → Bool
  | [] => false
  | b :: x => xor b (parity x)

theorem leaves_pos (T : DTree) : 1 ≤ T.leaves := by
  cases T with
  | leaf => exact Nat.le_refl 1
  | node lo hi =>
    have := leaves_pos lo
    simp only [DTree.leaves]; omega

/-- Any decision tree computing (possibly negated) parity on length `n` has at
least `2 ^ n` leaves; parity is in P, so table size is not algorithmic cost. -/
theorem parity_tree_leaves (n : Nat) (T : DTree) (c : Bool)
    (h : ∀ x, x.length = n → T.eval x = xor c (parity x)) : 2 ^ n ≤ T.leaves := by
  induction n generalizing T c with
  | zero => exact leaves_pos T
  | succ n ih =>
    cases T with
    | leaf b =>
      have h0 := h (false :: List.replicate n false) (by simp)
      have h1 := h (true :: List.replicate n false) (by simp)
      simp only [DTree.eval, parity] at h0 h1
      rw [h0] at h1
      cases c <;> cases parity (List.replicate n false) <;> simp at h1
    | node lo hi =>
      have hlo : ∀ x, x.length = n → lo.eval x = xor c (parity x) := by
        intro x hx
        have := h (false :: x) (by simp [hx])
        simp only [DTree.eval, parity] at this
        simpa using this
      have hhi : ∀ x, x.length = n → hi.eval x = xor (!c) (parity x) := by
        intro x hx
        have := h (true :: x) (by simp [hx])
        simp only [DTree.eval, parity, ite_true] at this
        rw [this]
        cases c <;> cases parity x <;> rfl
      have a1 := ih lo c hlo
      have a2 := ih hi (!c) hhi
      simp only [DTree.leaves, Nat.pow_succ]
      omega

/-- The complete tree for parity has exactly `2 ^ n` leaves, so the bound is tight. -/
theorem parity_tree_exact (n : Nat) : (build n parity).leaves = 2 ^ n := build_leaves n parity

/-- Every length-only language has one-bit advice: a one-node tree at every length. -/
theorem unary_one_bit (u : Nat → Bool) (n : Nat) :
    ∃ T : DTree, T.size = 1 ∧ ∀ x, x.length = n → T.eval x = u x.length :=
  ⟨.leaf (u n), rfl, fun x hx => by rw [hx]; rfl⟩

/-- For every enumeration of uniform deciders there is a length-only language
with one-node trees at every length that no enumerated decider computes. -/
theorem advice_beyond_uniform (e : Nat → List Bool → Bool) :
    ∃ L : List Bool → Bool,
      (∀ n, ∃ T : DTree, T.size = 1 ∧ ∀ x, x.length = n → T.eval x = L x) ∧
      ∀ i, e i ≠ L := by
  let u : Nat → Bool := fun n => !(e n (List.replicate n false))
  refine ⟨fun x => u x.length, ?_, ?_⟩
  · intro n
    exact unary_one_bit u n
  · intro i hi
    have := congrFun hi (List.replicate i false)
    simp only [u, List.length_replicate] at this
    cases h : e i (List.replicate i false) <;> rw [h] at this <;> simp at this

/-- Explicit polynomial bound `coefficient * (n + 1) ^ degree`. -/
structure Poly where
  coefficient : Nat
  degree : Nat

def Poly.eval (p : Poly) (n : Nat) : Nat := p.coefficient * (n + 1) ^ p.degree

/-- Schema for turning advice into a uniform algorithm: advice of polynomial
length produced by a generator in a caller-supplied class `Uniform`, and an
unrestricted decoder.  `Uniform` and `decode` are free, so the schema carries no
running-time content; the machine version is `UniformAdvice` below. -/
def UniformPolyAdviceFor (Uniform : (Nat → List Bool) → Prop) (L : List Bool → Bool) : Prop :=
  ∃ (gen : Nat → List Bool) (decode : List Bool → List Bool → Bool) (p : Poly),
    Uniform gen ∧ (∀ n, (gen n).length ≤ p.eval n) ∧
    ∀ x, decode (gen x.length) x = L x

/-- Unpacking the schema: a uniform generator and a decoder combine into a
single decider `x ↦ decode (gen |x|) x`, so meeting the schema already
means giving a uniform algorithm; advice contributes nothing beyond it. -/
theorem uniform_advice_decides (Uniform : (Nat → List Bool) → Prop) (L : List Bool → Bool)
    (h : UniformPolyAdviceFor Uniform L) :
    ∃ (gen : Nat → List Bool) (decode : List Bool → List Bool → Bool),
      Uniform gen ∧ ∀ x, decode (gen x.length) x = L x := by
  obtain ⟨gen, decode, _, hu, _, hc⟩ := h
  exact ⟨gen, decode, hu, hc⟩

/-! ## The machine model: uniformly generated polynomial advice -/

open Complexity

/-- Self-delimiting encoding of an advice string: each bit `b` becomes `1 b`,
and a final `0` ends the advice. -/
def pack : Word → Word
  | [] => [false]
  | b :: a => true :: b :: pack a

/-- Strip a packed advice prefix. -/
def unpack : Word → Word
  | true :: _ :: w => unpack w
  | false :: w => w
  | _ => []

theorem unpack_pack_append (a x : Word) : unpack (pack a ++ x) = x := by
  induction a with
  | nil => rfl
  | cons b a ih => exact ih

theorem length_pack (a : Word) : (pack a).length = 2 * a.length + 1 := by
  induction a with
  | nil => rfl
  | cons b a ih => simp only [pack, List.length_cons, ih]; omega

/-- The input `x` with the advice string `a` attached in front. -/
def adviceWord (a x : Word) : Word := pack a ++ x

theorem unpack_adviceWord (a x : Word) : unpack (adviceWord a x) = x :=
  unpack_pack_append a x

/-- Uniform polynomial advice in the machine model: a `Complexity.Machine` `m`
attaches the advice `adv |x|` to every input within `p` steps (so the advice is
generated uniformly and has polynomial length), and a machine `d` decides `L`
within `q` steps from the input with its advice attached. -/
def UniformAdvice (L : Language) : Prop :=
  ∃ (adv : Nat → Word) (m : Machine) (p : Polynomial) (d : Machine) (q : Polynomial),
    Machines.Computes m (fun x => adviceWord (adv x.length) x) p ∧
    Machines.DecidesOn d q (fun w => ∃ x, w = adviceWord (adv x.length) x)
      (fun w => L (unpack w))

/-- **Open obligation.** SAT has uniform polynomial advice: some length-indexed
advice is attached to every input by a polynomial-time `Complexity.Machine`, and
a polynomial-time machine decides SAT from the input with its advice. -/
def UniformSATAdvice : Prop := UniformAdvice Machines.SAT

/-- Uniformly generated polynomial advice gives a polynomial-time decider. -/
theorem inP_of_uniformAdvice {L : Language} (h : UniformAdvice L) : InP L := by
  obtain ⟨adv, m, p, d, q, hm, hd⟩ := h
  exact Machines.inP_of_promise_reduction hm (fun x => ⟨x, rfl⟩)
    (fun x => by show L x = L (unpack (adviceWord _ x)); rw [unpack_adviceWord]) hd

/-- **Conditional theorem.** The open obligation puts SAT in P. -/
theorem inP_sat_of_uniformSATAdvice (h : UniformSATAdvice) : InP Machines.SAT :=
  inP_of_uniformAdvice h

/-- **Conditional theorem.** With the hardness half of Cook–Levin, the open
obligation gives P = NP. -/
theorem pEqualsNP_of_uniformSATAdvice (hard : Machines.SATHard) (h : UniformSATAdvice) :
    PEqualsNP :=
  Machines.pEqualsNP_of_inP_sat hard (inP_sat_of_uniformSATAdvice h)

/-- Uniform advice is in particular non-uniform advice: with the known theorem
`pSubsetPPoly`, the language has polynomial-size circuits. -/
theorem inPPoly_of_uniformAdvice {L : Language}
    (h : UniformAdvice L) : Circuits.InPPoly L :=
  Circuits.pSubsetPPoly L (inP_of_uniformAdvice h)

/-- **Refutation route.** A superpolynomial circuit lower bound for SAT (together
with the proved theorem `pSubsetPPoly`) refutes the open obligation. -/
theorem not_uniformSATAdvice_of_superpoly
    (h : Circuits.SuperpolyLowerBound Machines.SAT) : ¬ UniformSATAdvice := fun hU =>
  (Circuits.superpoly_iff_not_inPPoly Machines.SAT).mp h (inPPoly_of_uniformAdvice hU)

/-- **Non-vacuity.** Some language has no uniform polynomial advice. -/
theorem not_forall_uniformAdvice : ¬ ∀ L : Language, UniformAdvice L := by
  intro h
  obtain ⟨L, hL⟩ := Machines.exists_not_inP
  exact hL (inP_of_uniformAdvice (h L))

/-- **Schema instance.** Machine-generated advice instantiates
`UniformPolyAdviceFor`, with `Uniform` the class of advice generators that a
polynomial-time machine can attach to the input and `decode` the language
decided by the query machine.  The length bound on the advice comes from the
running time (`Machines.computes_output_poly`). -/
theorem uniformPolyAdviceFor_of_uniformAdvice {L : Language} (h : UniformAdvice L) :
    UniformPolyAdviceFor
      (fun gen => ∃ (m : Machine) (p : Polynomial),
        Machines.Computes m (fun x => adviceWord (gen x.length) x) p)
      L := by
  obtain ⟨adv, m, p, d, q, hm, _⟩ := h
  obtain ⟨r, hr⟩ := Machines.computes_output_poly hm
  refine ⟨adv, fun a x => L (unpack (adviceWord a x)), ⟨r.coefficient, r.degree⟩,
    ⟨m, p, hm⟩, fun n => ?_, fun x => by show L (unpack (adviceWord _ x)) = L x; rw [unpack_adviceWord]⟩
  have hn := hr (List.replicate n false)
  simp only [List.length_replicate, adviceWord, List.length_append, length_pack] at hn
  show (adv n).length ≤ r.coefficient * (n + 1) ^ r.degree
  exact Nat.le_trans (by omega) hn

end Issue532.Idea31
