(** An abstract relativization schema, paired with the Lean file.
    [P] and [NP] are parameters for language classes in each oracle world.
    This does not formalize actual oracle machines or prove the historical
    relativization, natural-proof, or algebrization theorems. *)

From Stdlib Require Import Bool.
From proofs.experiments.issue532.rocq Require Import Machines.

Definition EqualAt {Oracle : Type} (P NP : Oracle -> Language -> Prop)
  (A : Oracle) : Prop := forall L, P A L <-> NP A L.

Definition SeparationAt {Oracle : Type} (P NP : Oracle -> Language -> Prop)
  (A : Oracle) : Prop := exists L, NP A L /\ ~ P A L.

Definition UniformEqualityProof {Oracle : Type} (P NP : Oracle -> Language -> Prop)
  (T : Oracle -> Prop) : Prop := forall A, T A -> EqualAt P NP A.

Definition UniformSeparationProof {Oracle : Type} (P NP : Oracle -> Language -> Prop)
  (T : Oracle -> Prop) : Prop := forall A, T A -> SeparationAt P NP A.

Theorem separation_refutes_uniform {Oracle : Type} {P NP : Oracle -> Language -> Prop}
  {T : Oracle -> Prop} {B : Oracle} (sep : SeparationAt P NP B) (hT : T B) :
  ~ UniformEqualityProof P NP T.
Proof.
  intro uniform. destruct sep as [L [hNP hNotP]].
  apply hNotP. apply (uniform B hT L). exact hNP.
Qed.

Theorem equality_refutes_uniform {Oracle : Type} {P NP : Oracle -> Language -> Prop}
  {T : Oracle -> Prop} {A : Oracle} (eq : EqualAt P NP A) (hT : T A) :
  ~ UniformSeparationProof P NP T.
Proof.
  intro uniform. destruct (uniform A hT) as [L [hNP hNotP]].
  apply hNotP. apply (eq L). exact hNP.
Qed.

(** An illustrative two-world countermodel, not an oracle-machine model. *)
Definition modelP (A : bool) (_ : Language) : Prop := A = true.
Definition modelNP (_ : bool) (_ : Language) : Prop := True.

Theorem model_equal : EqualAt modelP modelNP true.
Proof. intro L; split; intro h; [exact I | reflexivity]. Qed.

Theorem model_separates : SeparationAt modelP modelNP false.
Proof. exists SAT. split; [exact I | discriminate]. Qed.

Theorem constant_true_not_uniform :
  ~ UniformEqualityProof modelP modelNP (fun _ => True).
Proof. exact (separation_refutes_uniform model_separates I). Qed.

Theorem constant_true_not_uniform_separation :
  ~ UniformSeparationProof modelP modelNP (fun _ => True).
Proof. exact (equality_refutes_uniform model_equal I). Qed.

(** The invalid universal barrier claim of PR #41 fails for a false technique. *)
Theorem false_technique_counterexample : ~ (~ (False -> PEqualsNP)).
Proof. intro h. apply h. intro impossible. destruct impossible. Qed.
