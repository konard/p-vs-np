(*
  Forward formalization of Nicholas Argall's 2003 undecidability claim.

  The file records the claimed Goedel-style inference and isolates the
  unsupported bridge needed to conclude that P=NP is undecidable.
*)

Module ArgallProofAttempt.

Parameter Theory : Type.
Parameter Sentence : Type.

Parameter ZFC : Theory.
Parameter PeqNP : Sentence.

Parameter ExpressibleIn : Theory -> Sentence -> Prop.
Parameter Consistent : Theory -> Prop.
Parameter Complete : Theory -> Prop.
Parameter Proves : Theory -> Sentence -> Prop.
Parameter Refutes : Theory -> Sentence -> Prop.

Definition IndependentOf (T : Theory) (phi : Sentence) : Prop :=
  ~ Proves T phi /\ ~ Refutes T phi.

Parameter p_eq_np_is_expressible : ExpressibleIn ZFC PeqNP.

Parameter goedel_incompleteness_for_zfc :
  Consistent ZFC -> ~ Complete ZFC.

(*
  This is the invalid bridge in the argument. Incompleteness of a theory does
  not imply that every expressible sentence is independent of that theory.
*)
Parameter argall_bridge :
  forall (T : Theory) (phi : Sentence),
    ExpressibleIn T phi -> Consistent T -> ~ Complete T -> IndependentOf T phi.

Theorem claimed_p_eq_np_undecidable :
    Consistent ZFC -> IndependentOf ZFC PeqNP.
Proof.
  intro hzfc.
  apply (argall_bridge ZFC PeqNP).
  - exact p_eq_np_is_expressible.
  - exact hzfc.
  - exact (goedel_incompleteness_for_zfc hzfc).
Qed.

Parameter missing_specific_independence_argument :
  ~ Proves ZFC PeqNP /\ ~ Refutes ZFC PeqNP.

End ArgallProofAttempt.
