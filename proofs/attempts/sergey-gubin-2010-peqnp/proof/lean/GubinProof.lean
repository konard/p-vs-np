/-!
  Specification of the correspondence required by Gubin's proposed LP method.

  The earlier version asserted that Gubin's LP was asymmetric and that its
  integral vertices corresponded to tours, even though it encoded neither the
  LP constraints nor valid tours. It also derived P = NP through an admitted
  step. Those assertions have been withdrawn.

  This abstract specification can be instantiated only after the actual
  variables, inequalities, projection and tour encoding are formalized.
-/

namespace GubinAttempt

structure Candidate (Graph Tour Point : Type) where
  feasible : Graph → Point → Prop
  vertex : Graph → Point → Prop
  integral : Point → Prop
  encode : Graph → Tour → Point
  validTour : Graph → Tour → Prop

/-- The two directions of a tour/vertex correspondence. This is a definition,
    not a claim that Gubin's construction satisfies it. -/
def HasCorrespondence {Graph Tour Point : Type}
    (c : Candidate Graph Tour Point) : Prop :=
  (∀ g t, c.validTour g t →
    c.feasible g (c.encode g t) ∧ c.vertex g (c.encode g t) ∧
      c.integral (c.encode g t)) ∧
  (∀ g p, c.feasible g p → c.vertex g p → c.integral p →
    ∃ t, c.validTour g t ∧ c.encode g t = p)

end GubinAttempt
