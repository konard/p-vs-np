/-
  Forward formalization of Nicholas Argall's 2003 undecidability claim.

  The file records the claimed Goedel-style inference and isolates the
  unsupported bridge needed to conclude that P=NP is undecidable.
-/

namespace ArgallProofAttempt

axiom Theory : Type
axiom Sentence : Type

axiom ZFC : Theory
axiom PeqNP : Sentence

axiom ExpressibleIn : Theory -> Sentence -> Prop
axiom Consistent : Theory -> Prop
axiom Complete : Theory -> Prop
axiom Proves : Theory -> Sentence -> Prop
axiom Refutes : Theory -> Sentence -> Prop

def IndependentOf (T : Theory) (phi : Sentence) : Prop :=
  Not (Proves T phi) /\ Not (Refutes T phi)

-- Argall's reconstruction starts from the correct observation that P=NP can be
-- represented as a formal sentence.
axiom p_eq_np_is_expressible : ExpressibleIn ZFC PeqNP

-- A Goedel-style metatheorem: suitable theories are not complete.
axiom goedel_incompleteness_for_zfc : Consistent ZFC -> Not (Complete ZFC)

-- This is the invalid bridge in the argument. Incompleteness of a theory does
-- not imply that every expressible sentence is independent of that theory.
axiom argall_bridge :
  forall (T : Theory) (phi : Sentence),
    ExpressibleIn T phi -> Consistent T -> Not (Complete T) -> IndependentOf T phi

theorem claimed_p_eq_np_undecidable :
    Consistent ZFC -> IndependentOf ZFC PeqNP := by
  intro hzfc
  exact argall_bridge ZFC PeqNP p_eq_np_is_expressible hzfc
    (goedel_incompleteness_for_zfc hzfc)

-- What is missing is a theorem specifically about PeqNP, not a generic
-- consequence of incompleteness.
axiom missing_specific_independence_argument :
  Not (Proves ZFC PeqNP) /\ Not (Refutes ZFC PeqNP)

end ArgallProofAttempt
