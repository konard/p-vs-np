import proofs.experiments.issue532.lean.Idea16

/-!
# Issue #532, Idea 38: relativization audit (oracle query lower bound)

Deterministic oracle computations are modelled as adaptive decision trees over an
oracle `O : Nat → Bool`. This file proves the combinatorial core of the
Baker–Gill–Solovay (BGS) oracle separation:

* `shallow_tree_misses`: for every tree `T` and every `N`, if `depth T < N` then
  some position `j < N` is invisible to `T`: `T` answers the same on the
  all-false oracle and on the oracle that is true exactly at `j`.
* `no_shallow_tree_decides_or`: hence no tree of depth `< N` decides
  "`∃ j < N, O j = true`" for all oracles.
* `orTree_correct`, `orTree_depth`: depth `N` suffices, so the bound is exact;
  `verifier_one_query`: a nondeterministic guess needs only one query.
* `bgs_core`: every family of trees with polynomial depth `c · (n+1)^k` fails to
  decide the `2^n`-position OR problem at some `n`.
* `relativizing_cannot_decide`, `nonrelativizing_needed`: an abstract proof
  method whose theorems hold relative to every oracle cannot prove a statement
  that fails relative to some oracle. If a statement holds for one oracle and fails
  for another (as BGS show for `P = NP`), neither it nor its negation has a
  relativizing proof. `NonrelativizingIngredientFor` is the generic schema over a
  free proof method.

Machine part, on the oracle machines of Idea 16 (`Idea16.OMachine`, which extend
`Complexity.Machine` by a query instruction):

* `testVerifier`, `testVerifier_run`, `testLangO_inNPO`: an explicit oracle
  machine that makes one query shows `testLangO A ∈ NP^A` for every oracle `A`.
* `BGSTestSeparation`: the BGS stage construction for `testLangO`, stated as a
  known-theorem hypothesis. `bgsSeparation_of_testSeparation` turns it into
  `Idea16.BGSSeparation` (`P^B ≠ NP^B`).
* `machineRelativizing_cannot_settle`: under the BGS hypotheses, a method whose
  theorems hold relative to every oracle proves neither `P^A = NP^A` nor its
  negation for all oracles.

The diagonal construction of the oracle `B` and the oracle `A` with
`P^A = NP^A` are **not** formalized; they enter only as the named hypotheses
`BGSTestSeparation` and `Idea16.BGSCollapse`.
-/

namespace Issue532.Idea38

/-- Old sanity check: a property can hold in one oracle world and fail in another. -/
theorem tested :
    ∃ property : Bool → Prop, property false ∧ ¬ property true := by
  refine ⟨(fun oracle => oracle = false), rfl, ?_⟩
  decide

/-! ## Decision trees with oracle queries -/

/-- Adaptive oracle decision tree: a leaf answers; `query i t0 t1` asks `O i` and
continues in `t0` (answer `false`) or `t1` (answer `true`). -/
inductive Tree
  | leaf (b : Bool)
  | query (i : Nat) (t0 t1 : Tree)

/-- Evaluation of a tree against an oracle. -/
def Tree.eval (O : Nat → Bool) : Tree → Bool
  | .leaf b => b
  | .query i t0 t1 => if O i then t1.eval O else t0.eval O

/-- Depth = maximal number of queries along a path. -/
def Tree.depth : Tree → Nat
  | .leaf _ => 0
  | .query _ t0 t1 => max t0.depth t1.depth + 1

/-- Positions queried along the path followed on the all-false oracle. -/
def Tree.falsePath : Tree → List Nat
  | .leaf _ => []
  | .query i t0 _ => i :: t0.falsePath

/-- The empty oracle. -/
def allFalse : Nat → Bool := fun _ => false

/-- The oracle that is true exactly at `j`. -/
def single (j : Nat) : Nat → Bool := fun i => i == j

theorem falsePath_length (T : Tree) : T.falsePath.length ≤ T.depth := by
  induction T with
  | leaf b => simp [Tree.falsePath, Tree.depth]
  | query i t0 t1 ih0 _ =>
    simp only [Tree.falsePath, Tree.depth, List.length_cons]
    have := Nat.le_max_left t0.depth t1.depth
    omega

/-- A position not queried on the all-false path cannot be seen by the tree. -/
theorem eval_single_of_not_mem (T : Tree) (j : Nat) (hj : j ∉ T.falsePath) :
    T.eval (single j) = T.eval allFalse := by
  induction T with
  | leaf b => rfl
  | query i t0 t1 ih0 _ =>
    simp only [Tree.falsePath, List.mem_cons, not_or] at hj
    have hji : (i == j) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun h => hj.1 h.symm
    simp [Tree.eval, single, allFalse, hji]
    exact ih0 hj.2

/-- Counting: a list shorter than `N` misses some number below `N`. -/
theorem exists_not_mem (N : Nat) : ∀ L : List Nat, L.length < N → ∃ j, j < N ∧ j ∉ L := by
  induction N with
  | zero => intro L h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro L hL
    by_cases hN : N ∈ L
    · have hlen : (L.erase N).length < N := by
        rw [List.length_erase_of_mem hN]
        have := List.length_pos_of_mem hN
        omega
      obtain ⟨j, hj, hjL⟩ := ih (L.erase N) hlen
      refine ⟨j, Nat.lt_succ_of_lt hj, fun hmem => hjL ?_⟩
      exact (List.mem_erase_of_ne (Nat.ne_of_lt hj)).mpr hmem
    · exact ⟨N, Nat.lt_succ_self N, hN⟩

/-- **Shallow trees miss a position.** If `depth T < N`, some `j < N` is invisible:
`T` answers the same on the empty oracle and on the oracle true exactly at `j`. -/
theorem shallow_tree_misses (T : Tree) (N : Nat) (h : T.depth < N) :
    ∃ j, j < N ∧ T.eval allFalse = T.eval (single j) := by
  obtain ⟨j, hj, hjL⟩ :=
    exists_not_mem N T.falsePath (Nat.lt_of_le_of_lt (falsePath_length T) h)
  exact ⟨j, hj, (eval_single_of_not_mem T j hjL).symm⟩

/-- **Query lower bound (BGS core).** No tree of depth `< N` decides whether the
oracle has a `true` among positions `0, ..., N-1`. -/
theorem no_shallow_tree_decides_or (T : Tree) (N : Nat) (h : T.depth < N) :
    ¬ ∀ O : Nat → Bool, (T.eval O = true ↔ ∃ j, j < N ∧ O j = true) := by
  intro hdec
  obtain ⟨j, hj, heq⟩ := shallow_tree_misses T N h
  have h1 : T.eval (single j) = true := (hdec (single j)).mpr ⟨j, hj, by simp [single]⟩
  have h0 : T.eval allFalse ≠ true := by
    intro ht
    obtain ⟨_, _, hk⟩ := (hdec allFalse).mp ht
    simp [allFalse] at hk
  exact h0 (heq.trans h1)

/-! ## The bound is exact, and one nondeterministic query suffices -/

/-- Query positions `N-1, ..., 0` in turn. -/
def orTree : Nat → Tree
  | 0 => .leaf false
  | N + 1 => .query N (orTree N) (.leaf true)

theorem orTree_depth (N : Nat) : (orTree N).depth = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [orTree, Tree.depth, ih]

theorem orTree_correct (O : Nat → Bool) (N : Nat) :
    (orTree N).eval O = true ↔ ∃ j, j < N ∧ O j = true := by
  induction N with
  | zero => simp [orTree, Tree.eval]
  | succ N ih =>
    cases hN : O N with
    | true =>
      simp only [orTree, Tree.eval, hN, ite_true]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, hN⟩, fun _ => trivial⟩
    | false =>
      simp only [orTree, Tree.eval, hN, Bool.false_eq_true, ite_false]
      rw [ih]
      constructor
      · rintro ⟨j, hj, hOj⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hOj⟩
      · rintro ⟨j, hj, hOj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact ⟨j, hlt, hOj⟩
        · subst heq; rw [hN] at hOj; exact absurd hOj (by decide)

/-- **One nondeterministic query.** With a guessed position `j` as certificate, a
depth-1 tree verifies the OR problem. -/
theorem verifier_one_query (O : Nat → Bool) (N : Nat) :
    (∃ j, j < N ∧ O j = true) ↔
      ∃ j, j < N ∧ (Tree.query j (.leaf false) (.leaf true)).eval O = true := by
  constructor
  · rintro ⟨j, hj, hOj⟩
    exact ⟨j, hj, by simp [Tree.eval, hOj]⟩
  · rintro ⟨j, hj, hev⟩
    refine ⟨j, hj, ?_⟩
    cases hOj : O j with
    | true => rfl
    | false => simp [Tree.eval, hOj] at hev

/-! ## Polynomial depth against `2^n` positions -/

theorem succ_le_two_pow (q : Nat) : q + 1 ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.pow_succ]; omega

theorem lt_two_pow_self (a : Nat) : a < 2 ^ a := by
  have := succ_le_two_pow a
  omega

theorem linear_lt_exp (a q : Nat) (hq : 2 * a + 1 ≤ q) : a * (q + 1) < 2 ^ q := by
  obtain ⟨d, rfl⟩ : ∃ d, q = 2 * a + 1 + d := ⟨q - (2 * a + 1), by omega⟩
  induction d with
  | zero =>
    have h1 : a + 1 ≤ 2 ^ a := succ_le_two_pow a
    have h2 : a < 2 ^ a := lt_two_pow_self a
    have e : 2 ^ (2 * a + 1 + 0) = 2 ^ a * (2 * 2 ^ a) := by
      rw [show 2 * a + 1 + 0 = a + (a + 1) by omega, Nat.pow_add, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ a) 2]
    rw [e, show 2 * a + 1 + 0 + 1 = 2 * (a + 1) by omega]
    have h3 : 2 * (a + 1) ≤ 2 * 2 ^ a := by omega
    have hpos : 0 < 2 * 2 ^ a := by omega
    calc a * (2 * (a + 1)) ≤ a * (2 * 2 ^ a) := Nat.mul_le_mul_left a h3
      _ < 2 ^ a * (2 * 2 ^ a) := Nat.mul_lt_mul_of_pos_right h2 hpos
  | succ d ih =>
    have ih := ih (by omega)
    have ha : a ≤ a * (2 * a + 1 + d + 1) := Nat.le_mul_of_pos_right a (by omega)
    rw [show 2 * a + 1 + (d + 1) = (2 * a + 1 + d) + 1 by omega, Nat.pow_succ,
      Nat.mul_add, Nat.mul_one]
    omega

theorem dyadic_bracket (n : Nat) (hn : 1 ≤ n) : ∃ L, 2 ^ L ≤ n ∧ n < 2 ^ (L + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
  induction d with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ d ih =>
    obtain ⟨L, h1, h2⟩ := ih (by omega)
    by_cases h : 1 + (d + 1) < 2 ^ (L + 1)
    · exact ⟨L, by omega, h⟩
    · refine ⟨L + 1, by omega, ?_⟩
      rw [Nat.pow_succ 2 (L + 1)]
      omega

/-- `c * (n + 1) ^ k < 2 ^ n` for all `n ≥ 2 ^ (2 * (c + k) + 1)`. -/
theorem exp_beats_poly (c k : Nat) :
    ∀ n, 2 ^ (2 * (c + k) + 1) ≤ n → c * (n + 1) ^ k < 2 ^ n := by
  intro n hn
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.one_le_two_pow) hn
  obtain ⟨L, hL1, hL2⟩ := dyadic_bracket n hn1
  have hLbig : 2 * (c + k) + 1 ≤ L := by
    rcases Nat.lt_or_ge L (2 * (c + k) + 1) with hlt | hge
    · have : 2 ^ (L + 1) ≤ 2 ^ (2 * (c + k) + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hge
  have hlin : (c + k) * (L + 1) < 2 ^ L := linear_lt_exp (c + k) L hLbig
  have hsum : c + k * (L + 1) < n := by
    have : c + k * (L + 1) ≤ (c + k) * (L + 1) := by
      rw [Nat.add_mul]
      have : c ≤ c * (L + 1) := Nat.le_mul_of_pos_right c (by omega)
      omega
    omega
  have hbase : (n + 1) ^ k ≤ 2 ^ ((L + 1) * k) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) k
  have hc : c < 2 ^ c := lt_two_pow_self c
  have hpos : 0 < 2 ^ ((L + 1) * k) := Nat.two_pow_pos _
  calc c * (n + 1) ^ k ≤ c * 2 ^ ((L + 1) * k) := Nat.mul_le_mul_left c hbase
    _ < 2 ^ c * 2 ^ ((L + 1) * k) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = 2 ^ (c + (L + 1) * k) := (Nat.pow_add 2 c _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; omega)

/-- **BGS core, polynomial form.** For every family of trees whose depth is bounded by
`c · (n+1)^k`, there is an `n` at which the tree fails to decide whether the oracle has
a `true` among the first `2^n` positions. (A deterministic polynomial-time oracle machine
on input `1^n` is such a family; the language `{1^n : ∃ x ∈ {0,1}^n, x ∈ O}` is in `NP^O`.) -/
theorem bgs_core (trees : Nat → Tree) (c k : Nat)
    (hdepth : ∀ n, (trees n).depth ≤ c * (n + 1) ^ k) :
    ∃ n, ¬ ∀ O : Nat → Bool, ((trees n).eval O = true ↔ ∃ j, j < 2 ^ n ∧ O j = true) := by
  let n := 2 ^ (2 * (c + k) + 1)
  exact ⟨n, no_shallow_tree_decides_or (trees n) (2 ^ n)
    (Nat.lt_of_le_of_lt (hdepth n) (exp_beats_poly c k n (Nat.le_refl n)))⟩

/-! ## Relativizing proof methods -/

/-- A proof method (a predicate on oracle-indexed statements) relativizes if everything
it proves holds relative to every oracle. -/
def Relativizing (Proves : ((Nat → Bool) → Prop) → Prop) : Prop :=
  ∀ S, Proves S → ∀ O, S O

/-- A relativizing method cannot prove a statement that fails for some oracle. -/
theorem relativizing_cannot_prove (Proves : ((Nat → Bool) → Prop) → Prop)
    (hrel : Relativizing Proves) (S : (Nat → Bool) → Prop) (O : Nat → Bool) (hO : ¬ S O) :
    ¬ Proves S :=
  fun hS => hO (hrel S hS O)

/-- **BGS meta-theorem (abstract).** If `S` holds for oracle `A` and fails for oracle `B`,
a relativizing method proves neither `S` nor its negation. -/
theorem relativizing_cannot_decide (Proves : ((Nat → Bool) → Prop) → Prop)
    (hrel : Relativizing Proves) (S : (Nat → Bool) → Prop) (A B : Nat → Bool)
    (hA : S A) (hB : ¬ S B) :
    ¬ Proves S ∧ ¬ Proves (fun O => ¬ S O) :=
  ⟨relativizing_cannot_prove Proves hrel S B hB,
   relativizing_cannot_prove Proves hrel (fun O => ¬ S O) A (fun h => h hA)⟩

/-- Generic schema over a free proof method `Proves` (not a machine-level statement):
the method proves some statement that fails relative to some oracle. The
machine-level barrier is `machineRelativizing_cannot_settle`. -/
def NonrelativizingIngredientFor (Proves : ((Nat → Bool) → Prop) → Prop) : Prop :=
  ∃ S O, Proves S ∧ ¬ S O

/-- **Nonrelativizing ingredient needed.** A method that settles an oracle-dependent
statement is not relativizing. -/
theorem nonrelativizing_needed (Proves : ((Nat → Bool) → Prop) → Prop)
    (S : (Nat → Bool) → Prop) (A B : Nat → Bool) (hA : S A) (hB : ¬ S B)
    (hproof : Proves S ∨ Proves (fun O => ¬ S O)) :
    NonrelativizingIngredientFor Proves := by
  rcases hproof with h | h
  · exact ⟨S, B, h, hB⟩
  · exact ⟨fun O => ¬ S O, A, h, fun h' => h' hA⟩

/-- `NonrelativizingIngredientFor` is exactly the failure of `Relativizing` (classical). -/
theorem nonrelativizing_iff (Proves : ((Nat → Bool) → Prop) → Prop) :
    NonrelativizingIngredientFor Proves ↔ ¬ Relativizing Proves := by
  constructor
  · rintro ⟨S, O, hS, hO⟩ hrel
    exact hO (hrel S hS O)
  · intro hnot
    apply Classical.byContradiction
    intro hno
    apply hnot
    intro S hS O
    apply Classical.byContradiction
    intro hO
    exact hno ⟨S, O, hS, hO⟩

/-- Check: depth-2 tree `orTree 2` is correct on the oracle true only at `1`. -/
example : (orTree 2).eval (single 1) = true := by decide

/-! ## Machine part: the barrier on the oracle machines of Idea 16 -/

open Complexity Issue532.Machines
open Issue532.Idea16 (Oracle OInstruction OMachine oinstruction ostep ORun orun_deterministic
  queryWord InPO InNPO OVerifier PEqualsNPO BGSCollapse BGSSeparation)

/-- The verifier for `testLangO`: scan right over `x`, overwrite the separator
by `1`, scan back to the left end, and query the word `x ++ true :: cert`. -/
def testVerifier : OMachine :=
  ⟨[ [.base (.halt false), .base (.move 0 .zero .right), .base (.move 0 .one .right),
      .base (.move 1 .one .left)],
     [.base (.move 2 .blank .right), .base (.move 1 .zero .left), .base (.move 1 .one .left),
      .base (.halt false)],
     [.query 3 4, .query 3 4, .query 3 4, .query 3 4],
     [.base (.halt true), .base (.halt true), .base (.halt true), .base (.halt true)],
     [.base (.halt false), .base (.halt false), .base (.halt false), .base (.halt false)] ]⟩

/-- The configuration with state `q`, left part `L`, and the rest of the tape `s`
starting at the head. -/
def hc (q : Nat) (L : List Symbol) : List Symbol → Config
  | [] => ⟨q, L, .blank, []⟩
  | a :: r => ⟨q, L, a, r⟩

theorem moveHead_right (q q' : Nat) (L : List Symbol) (a w : Symbol) (r : List Symbol) :
    moveHead ⟨q, L, a, r⟩ q' w .right = hc q' (w :: L) r := by
  cases r <;> rfl

/-- The left scan target: moving left onto `ys` (nearest symbol first). -/
def lc (ys R : List Symbol) : Config :=
  match ys with
  | [] => ⟨1, [], .blank, R⟩
  | a :: rest => ⟨1, rest, a, R⟩

theorem ofBool_ne_sep (x : Bool) : Symbol.ofBool x ≠ .separator := by cases x <;> decide

theorem scan_right (A : Oracle) (cs : List Symbol) (t : Nat) (b : Bool) :
    ∀ (xs : List Bool) (L : List Symbol),
      ORun A testVerifier (hc 0 ((xs.map Symbol.ofBool).reverse ++ L) (.separator :: cs)) t b →
      ORun A testVerifier (hc 0 L (xs.map Symbol.ofBool ++ .separator :: cs)) (t + xs.length) b
  | [], L, h => by simpa using h
  | x :: xs, L, h => by
    have ih := scan_right A cs t b xs (Symbol.ofBool x :: L)
      (by simpa [List.reverse_cons, List.append_assoc] using h)
    have hs : ostep A testVerifier (hc 0 L (Symbol.ofBool (x) :: (xs.map Symbol.ofBool ++ .separator :: cs))) =
        .inr (hc 0 (Symbol.ofBool x :: L) (xs.map Symbol.ofBool ++ .separator :: cs)) := by
      cases x <;> simp [hc, ostep, oinstruction, testVerifier, Symbol.ofBool, Symbol.index,
        moveHead_right]
    have := ORun.next hs ih
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem scan_left (A : Oracle) (t : Nat) (b : Bool) :
    ∀ (ys : List Bool) (R : List Symbol),
      ORun A testVerifier ⟨1, [], .blank, (ys.map Symbol.ofBool).reverse ++ R⟩ t b →
      ORun A testVerifier (lc (ys.map Symbol.ofBool) R) (t + ys.length) b
  | [], R, h => by simpa [lc] using h
  | y :: ys, R, h => by
    have ih := scan_left A t b ys (Symbol.ofBool y :: R)
      (by simpa [List.reverse_cons, List.append_assoc] using h)
    have hs : ostep A testVerifier (lc (Symbol.ofBool y :: ys.map Symbol.ofBool) R) =
        .inr (lc (ys.map Symbol.ofBool) (Symbol.ofBool y :: R)) := by
      cases ys <;> cases y <;> simp [lc, ostep, oinstruction, testVerifier, Symbol.ofBool,
        Symbol.index, moveHead]
    have := ORun.next hs ih
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem queryWord_bits (xs : List Bool) (r : List Symbol) :
    queryWord (xs.map Symbol.ofBool ++ r) = xs ++ queryWord r := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [Symbol.ofBool, queryWord, ih]

/-- The explicit run: `2·|x| + 4` steps, answer `A (x ++ true :: cert)`. -/
theorem testVerifier_run (A : Oracle) (x cert : Word) :
    ORun A testVerifier (pairedInput x cert) (2 * x.length + 4) (A (x ++ true :: cert)) := by
  have hq : queryWord (x.map Symbol.ofBool ++ .one :: cert.map Symbol.ofBool) = x ++ true :: cert := by
    have hc' := queryWord_bits cert []
    simp only [List.append_nil] at hc'
    rw [queryWord_bits]
    simp [queryWord, hc']
  -- final three steps: blank → right, query, halt
  have hfin : ORun A testVerifier ⟨1, [], .blank, x.map Symbol.ofBool ++ .one :: cert.map Symbol.ofBool⟩
      3 (A (x ++ true :: cert)) := by
    have h1 : ostep A testVerifier ⟨1, [], .blank, x.map Symbol.ofBool ++ .one :: cert.map Symbol.ofBool⟩ =
        .inr (hc 2 [.blank] (x.map Symbol.ofBool ++ .one :: cert.map Symbol.ofBool)) := by
      simp only [ostep, oinstruction, testVerifier]
      cases x <;> rfl
    refine ORun.next h1 ?_
    generalize hz : x.map Symbol.ofBool ++ .one :: cert.map Symbol.ofBool = z at hq
    have hz' : z ≠ [] := by rw [← hz]; simp
    obtain ⟨a, r, rfl⟩ : ∃ a r, z = a :: r := by
      cases z with
      | nil => exact absurd rfl hz'
      | cons a r => exact ⟨a, r, rfl⟩
    have h2 : ostep A testVerifier (hc 2 [.blank] (a :: r)) =
        .inr ⟨if A (x ++ true :: cert) then 3 else 4, [.blank], a, r⟩ := by
      simp only [hc, ostep, oinstruction, testVerifier, hq]
      cases a <;> rfl
    refine ORun.next h2 (ORun.halt ?_)
    cases hA : A (x ++ true :: cert) <;> cases a <;> rfl
  have h2 := scan_left A 3 (A (x ++ true :: cert)) x.reverse (.one :: cert.map Symbol.ofBool)
    (by simpa [List.map_reverse] using hfin)
  -- the separator step
  have hsep : ostep A testVerifier (hc 0 ((x.map Symbol.ofBool).reverse ++ []) (.separator :: cert.map Symbol.ofBool)) =
      .inr (lc (x.reverse.map Symbol.ofBool) (.one :: cert.map Symbol.ofBool)) := by
    rw [List.map_reverse]
    simp only [hc, ostep, oinstruction, testVerifier, List.append_nil]
    cases (x.map Symbol.ofBool).reverse <;> rfl
  have h3 := scan_right A (cert.map Symbol.ofBool) _ _ x [] (ORun.next hsep h2)
  have hinit : pairedInput x cert = hc 0 [] (x.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool) := by
    simp only [pairedInput, List.append_assoc, List.singleton_append]
    cases x.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool <;> rfl
  rw [hinit]
  simp only [List.length_reverse] at h3
  have he : 3 + x.length + 1 + x.length = 2 * x.length + 4 := by omega
  rw [he] at h3
  exact h3


open Classical in
/-- The BGS-style test language relative to `A`: some extension `x ++ true :: y`
with `|y| ≤ |x| + 1` is in `A`. Distinct inputs `0^n` have disjoint candidate sets,
which is what the BGS stage construction needs. -/
noncomputable def testLangO (A : Oracle) : Language := fun x =>
  decide (∃ y : Word, y.length ≤ x.length + 1 ∧ A (x ++ true :: y) = true)

/-- **The NP side, in the machine model (proved).** For every oracle `A`,
`testLangO A ∈ NP^A`, witnessed by the explicit oracle machine `testVerifier` making
one query. This is the machine form of `verifier_one_query`. -/
theorem testLangO_inNPO (A : Oracle) : InNPO A (testLangO A) := by
  refine ⟨.paired testVerifier, ⟨4, 1⟩, ⟨1, 1⟩, fun x cert _ => ?_, fun x => ?_⟩
  · refine ⟨2 * x.length + 4, _, ?_, testVerifier_run A x cert⟩
    simp only [OVerifier.timeLimit, Polynomial.eval, Nat.pow_one]
    omega
  · constructor
    · intro h
      simp only [testLangO, decide_eq_true_eq] at h
      obtain ⟨y, hy, hA⟩ := h
      refine ⟨y, 2 * x.length + 4, ?_, ?_, ?_⟩
      · simp only [Polynomial.eval, Nat.pow_one, Nat.one_mul]; exact hy
      · simp only [OVerifier.timeLimit, Polynomial.eval, Nat.pow_one]; omega
      · have := testVerifier_run A x y
        rw [hA] at this
        exact this
    · rintro ⟨cert, t, hc, _, hr⟩
      have hr' := testVerifier_run A x cert
      have hb := (orun_deterministic hr hr').2
      simp only [testLangO, decide_eq_true_eq]
      exact ⟨cert, by simpa [Polynomial.eval] using hc, hb.symm⟩

/-- **Known theorem, not mechanised here** (the stage construction of Baker, Gill,
Solovay, SIAM J. Comput. 4(4), 1975, applied to the test language
`testLangO`): there is an oracle `B` with `testLangO B ∉ P^B`. Its query-complexity
core is `bgs_core`: a polynomial-time machine makes fewer than `2^n` queries, so at
some input `0^n` it misses an unqueried candidate `0^n ++ true :: y`. -/
def BGSTestSeparation : Prop := ∃ B : Oracle, ¬ InPO B (testLangO B)

/-- The test separation gives the BGS separation `P^B ≠ NP^B` of the shared model. -/
theorem bgsSeparation_of_testSeparation (h : BGSTestSeparation) : BGSSeparation := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun hP => hB (hP _ (testLangO_inNPO B))⟩

/-- A proof method over machine-oracle statements relativizes if everything it
proves holds relative to every oracle. -/
def MachineRelativizing (Proves : (Oracle → Prop) → Prop) : Prop :=
  ∀ S, Proves S → ∀ A, S A

/-- **BGS barrier for machine statements.** Under the known BGS theorems, a
relativizing method proves neither `P^A = NP^A` nor `P^A ≠ NP^A` as statements
about all oracles. Its only relativizing route to the real question
(`Idea16.pEqualsNP_of_all_oracles`, `Idea16.pNotEqualsNP_of_all_oracles`) is closed. -/
theorem machineRelativizing_cannot_settle (Proves : (Oracle → Prop) → Prop)
    (hrel : MachineRelativizing Proves) (h1 : BGSCollapse) (h2 : BGSTestSeparation) :
    ¬ Proves PEqualsNPO ∧ ¬ Proves (fun A => ¬ PEqualsNPO A) := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := bgsSeparation_of_testSeparation h2
  exact ⟨fun h => hB (hrel _ h B), fun h => hrel _ h A hA⟩

end Issue532.Idea38
