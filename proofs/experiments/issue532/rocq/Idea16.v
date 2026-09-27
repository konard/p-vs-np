(* Issue #532, Idea 16: diagonalization and relativization.

   Rocq counterpart of lean/Idea16.lean; theorem names are aligned.

   Proved in general: the Cantor/Turing diagonal differs from every enumerated
   language; the abstract hierarchy theorem (the diagonal of an enumerated
   class is decidable with one query to a universal evaluator but is not in
   the class); both arguments hold in every oracle world (they relativize);
   a relativizing technique cannot prove a statement that fails in some world;
   and the query-complexity core of the Baker-Gill-Solovay oracle: every
   decision tree with fewer than 2^n queries errs on the test language for
   some oracle.

   Verdict: with Baker-Gill-Solovay (1975, not formalized), pure
   diagonalization cannot settle P vs NP.  The non-relativizing ingredient is
   an open obligation, stated as a definition only.  Nothing here proves or
   refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.

(** * Cantor/Turing diagonal *)

Definition diag (e : nat -> nat -> bool) : nat -> bool := fun n => negb (e n n).

(** The diagonal language differs from every enumerated language. *)
Theorem diag_ne : forall (e : nat -> nat -> bool) i, diag e <> e i.
Proof.
  intros e i h. assert (h1 : diag e i = e i i) by (rewrite h; reflexivity).
  unfold diag in h1. destruct (e i i); discriminate.
Qed.

(** No enumeration lists all languages. *)
Theorem no_enumeration_of_all : forall (e : nat -> nat -> bool),
  exists L : nat -> bool, forall i, e i <> L.
Proof. intro e. exists (diag e). intros i h. apply (diag_ne e i). symmetry. exact h. Qed.

(** * Abstract hierarchy theorem *)

Definition Enumerates (e : nat -> nat -> bool) (C : (nat -> bool) -> Prop) : Prop :=
  (forall i, C (e i)) /\ forall L, C L -> exists i, e i = L.

Definition OneQuery (u : nat -> nat -> bool) (L : nat -> bool) : Prop :=
  exists (a : nat -> nat) (g : bool -> bool), forall x, L x = g (u (a x) x).

(** The diagonal is decidable with one query to [u] and not in [C]. *)
Theorem hierarchy_abstract : forall (e u : nat -> nat -> bool) (C : (nat -> bool) -> Prop),
  (forall i x, u i x = e i x) -> Enumerates e C ->
  OneQuery u (fun x => negb (u x x)) /\ ~ C (fun x => negb (u x x)).
Proof.
  intros e u C hu [_ hC]. split.
  - exists (fun x => x), negb. intro x. reflexivity.
  - intro hD. destruct (hC _ hD) as [i hi].
    assert (h1 : e i i = negb (u i i)) by (rewrite hi; reflexivity).
    rewrite hu in h1. destruct (e i i); discriminate.
Qed.

(** The hierarchy is strict. *)
Theorem hierarchy_strict : forall (e u : nat -> nat -> bool) (C : (nat -> bool) -> Prop),
  (forall i x, u i x = e i x) -> Enumerates e C ->
  (forall L, C L -> OneQuery u L) /\ exists L, OneQuery u L /\ ~ C L.
Proof.
  intros e u C hu hC. split.
  - intros L hL. destruct ((proj2 hC) L hL) as [i hi].
    exists (fun _ => i), (fun b => b). intro x. rewrite <- hi, hu. reflexivity.
  - exists (fun x => negb (u x x)). apply (hierarchy_abstract e u C hu hC).
Qed.

(** * Oracle worlds and relativization *)

Definition World := nat -> bool.

Definition Relativizes (S : World -> Prop) : Prop := forall O, S O.

Theorem no_relativizing_proof : forall (S : World -> Prop),
  (exists O, ~ S O) -> ~ Relativizes S.
Proof. intros S [O hO] hS. exact (hO (hS O)). Qed.

Theorem neither_relativizes : forall (S : World -> Prop),
  (exists A, ~ S A) -> (exists B, S B) ->
  ~ Relativizes S /\ ~ Relativizes (fun O => ~ S O).
Proof.
  intros S hA [B hB]. split.
  - exact (no_relativizing_proof S hA).
  - intro h. exact (h B hB).
Qed.

Theorem diag_relativizes : forall (eO : World -> nat -> nat -> bool),
  Relativizes (fun O => forall i, diag (eO O) <> eO O i).
Proof. intros eO O i. apply diag_ne. Qed.

Theorem hierarchy_relativizes : forall (eO uO : World -> nat -> nat -> bool)
  (CO : World -> (nat -> bool) -> Prop),
  (forall O i x, uO O i x = eO O i x) -> (forall O, Enumerates (eO O) (CO O)) ->
  Relativizes (fun O => OneQuery (uO O) (fun x => negb (uO O x x)) /\
                        ~ CO O (fun x => negb (uO O x x))).
Proof. intros eO uO CO hu hC O. exact (hierarchy_abstract (eO O) (uO O) (CO O) (hu O) (hC O)). Qed.

Definition Technique := (World -> Prop) -> Prop.

Definition Relativizing (T : Technique) : Prop := forall S, T S -> Relativizes S.

Definition DiagTech : Technique := fun S =>
  (exists eO : World -> nat -> nat -> bool,
     forall O, S O <-> forall i, diag (eO O) <> eO O i) \/
  (exists (eO uO : World -> nat -> nat -> bool) (CO : World -> (nat -> bool) -> Prop),
     (forall O i x, uO O i x = eO O i x) /\ (forall O, Enumerates (eO O) (CO O)) /\
     forall O, S O <-> (OneQuery (uO O) (fun x => negb (uO O x x)) /\
                        ~ CO O (fun x => negb (uO O x x)))).

(** Pure diagonalization is a relativizing technique. *)
Theorem diagTech_relativizing : Relativizing DiagTech.
Proof.
  intros S hS O. destruct hS as [[eO h] | [eO [uO [CO [hu [hC h]]]]]].
  - apply (proj2 (h O)). apply (diag_relativizes eO O).
  - apply (proj2 (h O)). apply (hierarchy_relativizes eO uO CO hu hC O).
Qed.

Theorem relativizing_cannot_prove : forall (T : Technique), Relativizing T ->
  forall (S : World -> Prop), (exists O, ~ S O) -> ~ T S.
Proof. intros T hT S h hS. exact (no_relativizing_proof S h (hT S hS)). Qed.

(** Pure diagonalization cannot prove a statement that fails in some world. *)
Theorem diagonalization_cannot_prove : forall (S : World -> Prop),
  (exists O, ~ S O) -> ~ DiagTech S.
Proof. intros S h. exact (relativizing_cannot_prove DiagTech diagTech_relativizing S h). Qed.

(** Open obligation (not assumed): a sound, non-relativizing technique proving [S]. *)
Definition NonRelativizingIngredient (T : Technique) (real : World) (S : World -> Prop) : Prop :=
  (forall S', T S' -> S' real) /\ T S /\ ~ Relativizing T.

Theorem ingredient_necessary : forall (T : Technique) (S : World -> Prop),
  (exists O, ~ S O) -> T S -> ~ Relativizing T.
Proof. intros T S h hT hR. exact (relativizing_cannot_prove T hR S h hT). Qed.

(** * The query-complexity core of the BGS oracle *)

Inductive QT : Type :=
  | Leaf : bool -> QT
  | Query : nat -> QT -> QT -> QT.

Fixpoint run (O : World) (t : QT) : bool :=
  match t with
  | Leaf b => b
  | Query q t1 t2 => if O q then run O t1 else run O t2
  end.

Fixpoint qdepth (t : QT) : nat :=
  match t with
  | Leaf _ => 0
  | Query _ t1 t2 => Nat.max (qdepth t1) (qdepth t2) + 1
  end.

Fixpoint path (O : World) (t : QT) : list nat :=
  match t with
  | Leaf _ => []
  | Query q t1 t2 => q :: (if O q then path O t1 else path O t2)
  end.

Theorem path_length : forall O t, length (path O t) <= qdepth t.
Proof.
  intros O t. induction t as [b | q t1 IH1 t2 IH2]; simpl; [lia|].
  destruct (O q); lia.
Qed.

Theorem run_agree : forall (O O' : World) t,
  (forall q, In q (path O t) -> O' q = O q) -> run O' t = run O t.
Proof.
  intros O O' t. induction t as [b | q t1 IH1 t2 IH2]; intro h; simpl; [reflexivity|].
  assert (hq : O' q = O q) by (apply h; simpl; left; reflexivity).
  rewrite hq. destruct (O q) eqn:hb.
  - apply IH1. intros p hp. apply h. simpl. rewrite hb. right. exact hp.
  - apply IH2. intros p hp. apply h. simpl. rewrite hb. right. exact hp.
Qed.

Fixpoint anyB (p : nat -> bool) (m : nat) : bool :=
  match m with 0 => false | S k => anyB p k || p k end.

Theorem anyB_iff : forall p m, anyB p m = true <-> exists y, y < m /\ p y = true.
Proof.
  intros p m. induction m as [|m IH]; simpl.
  - split; [discriminate | intros [y [hy _]]; lia].
  - rewrite orb_true_iff, IH. split.
    + intros [[y [hy hp]] | hp]; [exists y; split; [lia|exact hp] | exists m; split; [lia|exact hp]].
    + intros [y [hy hp]]. destruct (Nat.eq_dec y m) as [e | ne].
      * right. rewrite <- e. exact hp.
      * left. exists y. split; [lia|exact hp].
Qed.

Definition testLang (O : World) (n : nat) : bool := anyB (fun y => O (2 ^ n + y)) (2 ^ n).

Theorem testLang_one_certificate : forall O n,
  testLang O n = true <-> exists y, y < 2 ^ n /\ O (2 ^ n + y) = true.
Proof. intros O n. apply anyB_iff. Qed.

Theorem exists_unqueried : forall a m (l : list nat), length l < m ->
  exists y, y < m /\ ~ In (a + y) l.
Proof.
  intros a m. induction m as [|m IH]; intros l h; [lia|].
  destruct (in_dec Nat.eq_dec (a + m) l) as [hm | hm].
  - pose proof (remove_length_lt Nat.eq_dec l (a + m) hm) as hlen.
    destruct (IH (remove Nat.eq_dec (a + m) l) ltac:(lia)) as [y [hy hny]].
    exists y. split; [lia|]. intro hin. apply hny.
    apply in_in_remove; [lia | exact hin].
  - exists m. split; [lia | exact hm].
Qed.

(** Every decision tree with fewer than 2^n queries errs on the test language for some oracle. *)
Theorem oracle_adversary : forall n t, qdepth t < 2 ^ n ->
  exists O : World, run O t <> testLang O n.
Proof.
  intros n t ht.
  set (O0 := (fun _ : nat => false) : World).
  assert (h0 : testLang O0 n = false).
  { destruct (testLang O0 n) eqn:e; [|reflexivity].
    apply testLang_one_certificate in e. destruct e as [y [_ hy]]. discriminate hy. }
  destruct (run O0 t) eqn:h.
  - exists O0. rewrite h, h0. discriminate.
  - pose proof (path_length O0 t) as hl.
    destruct (exists_unqueried (2 ^ n) (2 ^ n) (path O0 t) ltac:(lia)) as [y [hy hny]].
    set (O1 := (fun z => Nat.eqb z (2 ^ n + y)) : World).
    assert (hagree : forall q, In q (path O0 t) -> O1 q = O0 q).
    { intros q hq. unfold O1, O0. apply Nat.eqb_neq. intro e. apply hny. rewrite <- e. exact hq. }
    assert (h1 : testLang O1 n = true).
    { apply testLang_one_certificate. exists y. split; [exact hy|]. unfold O1. apply Nat.eqb_refl. }
    exists O1. rewrite (run_agree O0 O1 t hagree), h, h1. discriminate.
Qed.
