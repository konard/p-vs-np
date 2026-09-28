import Init.Data.Nat.Lemmas

/-
  Vega (2015), Definition 3.1 and Theorems 5.3/6.2: semantic audit.

  These toy predicates omit polynomial runtime and certificate-length bounds;
  the results below are logical tests of the class-inclusion argument, not a
  formal complexity-theoretic refutation of Vega's full construction.
-/

namespace VegaRefutation

abbrev Instance := String
abbrev Certificate := String
abbrev Language := Instance → Prop
abbrev PairLanguage := (Instance × Instance) → Prop
abbrev Verifier := Instance → Certificate → Bool

def InP (L : Language) : Prop :=
  ∃ d : Instance → Bool, ∀ x, L x ↔ d x = true

def InEquivalentP (L : PairLanguage) : Prop :=
  ∃ (L1 L2 : Language) (M1 M2 : Verifier),
    InP L1 ∧ InP L2 ∧
    ∀ x y, L (x, y) ↔
      L1 x ∧ L2 y ∧ ∃ z, M1 x z = true ∧ M2 y z = true

def diagonal (L : Language) : PairLanguage :=
  fun (x, y) => x = y ∧ L x

-- A P decider may ignore its certificate. This shows that a product pair
-- language satisfies the toy Definition 3.1; it does not say every member of
-- equivalent-P is a product, since other verifiers may inspect certificates.
theorem product_of_P_languages_in_equivalentP
    (L1 L2 : Language) (h1 : InP L1) (h2 : InP L2) :
    InEquivalentP (fun (x, y) => L1 x ∧ L2 y) := by
  obtain ⟨d1, hd1⟩ := h1
  obtain ⟨d2, hd2⟩ := h2
  refine ⟨L1, L2, fun x _ => d1 x, fun y _ => d2 y,
    ⟨d1, hd1⟩, ⟨d2, hd2⟩, ?_⟩
  intro x y
  constructor
  · intro ⟨hx, hy⟩
    exact ⟨hx, hy, "", (hd1 x).mp hx, (hd2 y).mp hy⟩
  · intro ⟨hx, hy, _, _, _⟩
    exact ⟨hx, hy⟩

-- Conversely, the same toy definition can represent a diagonal by requiring
-- the common certificate to equal both inputs. Thus a missing proof with
-- certificate-ignoring verifiers is not a counterexample to Theorem 6.1.
theorem diagonal_P_in_equivalentP
    (L : Language) (h : InP L) : InEquivalentP (diagonal L) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨L, L,
    (fun x z => d x && decide (z = x)),
    (fun y z => d y && decide (z = y)),
    ⟨d, hd⟩, ⟨d, hd⟩, ?_⟩
  intro x y
  constructor
  · intro ⟨hxy, hx⟩
    subst y
    refine ⟨hx, hx, x, ?_, ?_⟩
    · simp [(hd x).mp hx]
    · simp [(hd x).mp hx]
  · intro ⟨hx, _, z, hzx, hzy⟩
    simp at hzx hzy
    exact ⟨hzx.2.symm.trans hzy.2, hx⟩

-- Applying a non-injective single-string reduction to both coordinates need
-- not preserve the diagonal predicate. The paper's e-reduction has a separate
-- pair-domain specification; no general transfer theorem is supplied here.
def constantMap (_ : Instance) : Instance := ""
def universalLanguage : Language := fun _ => True

theorem naive_diagonal_reduction_fails :
    ¬ diagonal universalLanguage ("a", "b") ∧
    diagonal universalLanguage (constantMap "a", constantMap "b") := by
  constructor
  · intro h
    exact (by decide : "a" ≠ "b") h.1
  · exact ⟨rfl, trivial⟩

-- A concrete countermodel to the inference used after the completeness
-- claims: membership of both a P-class and an NP-class in a common class
-- yields only inclusions. It cannot supply the reverse inclusion needed for
-- equivalent-P = P. Fin 2 is a logical model, not an actual complexity class.
def smallP (x : Fin 2) : Prop := x = 0
def smallNP (_ : Fin 2) : Prop := True
def commonClass (_ : Fin 2) : Prop := True

theorem two_inclusions_do_not_give_equality :
    (∀ x, smallP x → commonClass x) ∧
    (∀ x, smallNP x → commonClass x) ∧
    ¬ (∀ x, smallP x ↔ smallNP x) := by
  unfold smallP smallNP commonClass
  decide

end VegaRefutation
