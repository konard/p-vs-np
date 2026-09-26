/-
  Audit of Plotnikov's 2007 P=NP argument. The predicates below name the
  mathematical obligations in the paper; they do not implement its algorithm.
  No missing obligation is introduced as an axiom.
-/

namespace PlotnikovRefutation

def TimeComplexity := Nat → Nat

def isPolynomial (T : TimeComplexity) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

/- An instance represents a VS-digraph and its initiating set V⁰. The graph,
   fictitious-arc type, and induced set size remain abstract; a full audit
   must link them to an implementation of the paper's construction. -/
structure VSInstance where
  initialSize : Nat
  largerIndependentSet : Prop
  FictitiousArc : Type
  inducedSize : FictitiousArc → Nat

def QualifyingArc (i : VSInstance) : Prop :=
  ∃ arc : i.FictitiousArc, i.inducedSize arc ≥ i.initialSize - 1

def Conjecture1 (validInstance : VSInstance → Prop) : Prop :=
  ∀ i : VSInstance, validInstance i → i.largerIndependentSet → QualifyingArc i

/- Graph is an input graph, inLn restricts it to the paper's graph class Lₙ,
   and findsMMIS says that the proposed algorithm returns a maximum
   independent set. None of these predicates is established here. -/
def AlgorithmCorrect (Graph : Type) (inLn findsMMIS : Graph → Prop) : Prop :=
  ∀ g : Graph, inLn g → findsMMIS g

/- Theorem 5 has the form Conjecture 1 → algorithm correctness. This theorem
   makes both that implication and Conjecture 1 explicit proof obligations.
   A missing proof of Conjecture 1 does not imply that the conjecture is false
   or that the algorithm is incorrect. -/
theorem correctness_if_conjecture
    {Graph : Type}
    {validInstance : VSInstance → Prop}
    {inLn findsMMIS : Graph → Prop}
    (theorem5 : Conjecture1 validInstance → AlgorithmCorrect Graph inLn findsMMIS)
    (conjecture1 : Conjecture1 validInstance) :
    AlgorithmCorrect Graph inLn findsMMIS :=
  theorem5 conjecture1

/- In particular, the converse inference in the old axiom is invalid even
   when a conditional correctness implication is supplied. -/
theorem missing_conjecture_does_not_refute_algorithm :
    ¬ (∀ C A : Prop, (C → A) → ¬ C → ¬ A) := by
  intro h
  have notFalse : ¬ False := by
    intro f
    exact f
  exact h False True (by intro f; exact f.elim) notFalse True.intro

/- An assumption of correctness only yields that same assumption. It cannot
   establish an arbitrary conclusion without an independent premise. -/
theorem identity_implication (P : Prop) : P → P := by
  intro h
  exact h

theorem identity_does_not_establish_claim :
    ¬ (∀ P : Prop, (P → P) → P) := by
  intro h
  exact h False (identity_implication False)

/- The statement that a particular running time is polynomial needs a bound
   on that running time. An unproved correctness conjecture alone supplies no
   bound, and its negation does not imply a superpolynomial running time. -/
theorem polynomial_time_if_bound (T : TimeComplexity)
    (bound : ∀ n : Nat, T n ≤ n ^ 8) : isPolynomial T := by
  refine ⟨1, 8, ?_⟩
  intro n
  simpa using bound n

/- The old refutation negated polynomiality of this cubic function. -/
theorem cubic_is_polynomial : isPolynomial (fun n => n ^ 3) := by
  refine ⟨1, 3, ?_⟩
  intro n
  simp

end PlotnikovRefutation
