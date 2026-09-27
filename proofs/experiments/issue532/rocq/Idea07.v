(* Issue #532, Idea 07: lossless compression (pigeonhole and incompressibility).

   Proved for all parameters:
   - allStrings n lists the 2^n strings of length n without repetition, and
     shorter n lists the 2^n - 1 strings of length < n
     (length_allStrings, length_shorter);
   - pigeonhole: a duplicate-free list contained in M is no longer than M;
   - no_universal_compression: an encoder injective on length-n strings
     leaves some length-n string unshortened; shortening_forces_collision:
     an encoder shortening every length-n string merges two of them;
   - count_describable_le: for every decoder, at most 2^m - 1 strings of
     length n have a description shorter than m bits;
     incompressible_exists: some length-n string has no description shorter
     than n bits;
   - positive side: runs of one repeated bit are identified by a one-bit
     code (runCode_injective_on_runs).

   Verdict: refuted as a route (general theorem). *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.


Definition str_eq_dec : forall x y : list bool, {x = y} + {x <> y} :=
  list_eq_dec Bool.bool_dec.

Fixpoint allStrings (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allStrings n') ++ map (cons true) (allStrings n')
  end.

Fixpoint shorter (n : nat) : list (list bool) :=
  match n with
  | 0 => []
  | S n' => shorter n' ++ allStrings n'
  end.

Theorem length_allStrings (n : nat) : length (allStrings n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allStrings_iff (n : nat) (v : list bool) :
  In v (allStrings n) <-> length v = n.
Proof.
  revert v; induction n as [|n IH]; intros v.
  - destruct v as [|b v]; simpl; split; intros H; auto; try discriminate.
    destruct H as [H|H]; [discriminate|contradiction].
  - destruct v as [|b v]; simpl; rewrite in_app_iff, !in_map_iff; split.
    + intros [[w [Hw _]]|[w [Hw _]]]; discriminate.
    + intros H; discriminate.
    + intros [[w [Hw Hin]]|[w [Hw Hin]]]; injection Hw; intros; subst;
        f_equal; apply IH; auto.
    + intros H; injection H; intros H'; destruct b.
      * right; exists v; split; auto; apply IH; auto.
      * left; exists v; split; auto; apply IH; auto.
Qed.

Lemma nodup_app_intro {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 H; simpl; auto.
  inversion H1; subst. constructor.
  - intros Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + contradiction.
    + apply (H x); simpl; auto.
  - apply IH; auto. intros y Hy; apply H; simpl; auto.
Qed.

Lemma nodup_map_cons (b : bool) (L : list (list bool)) :
  NoDup L -> NoDup (map (cons b) L).
Proof.
  induction L as [|x L IH]; intros H; simpl; constructor.
  - inversion H; subst. intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Hy Hin]]; injection Hy; intros; subst; contradiction.
  - inversion H; subst; auto.
Qed.

Theorem nodup_allStrings (n : nat) : NoDup (allStrings n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [simpl; auto | constructor].
  - apply nodup_app_intro; try apply nodup_map_cons; auto.
    intros x Hx Hy; apply in_map_iff in Hx; apply in_map_iff in Hy.
    destruct Hx as [u [Hu _]]; destruct Hy as [w [Hw _]]; subst.
    discriminate.
Qed.

Lemma one_le_pow2 (n : nat) : 1 <= 2 ^ n.
Proof. induction n; simpl; lia. Qed.

Theorem length_shorter (n : nat) : length (shorter n) = 2 ^ n - 1.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, IH, length_allStrings.
  pose proof (one_le_pow2 n). lia.
Qed.

Theorem mem_shorter_iff (n : nat) (v : list bool) : In v (shorter n) <-> length v < n.
Proof.
  induction n as [|n IH]; simpl.
  - split; [contradiction | lia].
  - rewrite in_app_iff, IH, mem_allStrings_iff. lia.
Qed.

(* Pigeonhole principle over lists. *)
Theorem pigeonhole {A : Type} (L M : list A) :
  NoDup L -> (forall x, In x L -> In x M) -> length L <= length M.
Proof.
  intros HL Hsub. apply NoDup_incl_length; [exact HL | exact Hsub].
Qed.

Theorem nodup_map_of_injOn {A B : Type} (f : A -> B) (L : list A) :
  NoDup L -> (forall x y, In x L -> In y L -> f x = f y -> x = y) ->
  NoDup (map f L).
Proof.
  induction L as [|x L IH]; intros HL Hinj; simpl; constructor.
  - inversion HL; subst. intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Hy Hin]].
    assert (y = x) as E by (apply Hinj; simpl; auto).
    subst; contradiction.
  - inversion HL; subst. apply IH; auto.
    intros a b Ha Hb Hab; apply Hinj; simpl; auto.
Qed.

(* No lossless compressor shortens every string. *)
Definition InjectiveOnLength (enc : list bool -> list bool) (n : nat) : Prop :=
  forall x y, length x = n -> length y = n -> enc x = enc y -> x = y.

Theorem no_universal_compression (enc : list bool -> list bool) (n : nat) :
  InjectiveOnLength enc n -> exists x : list bool, length x = n /\ n <= length (enc x).
Proof.
  intros Hinj.
  destruct (existsb (fun x => n <=? length (enc x)) (allStrings n)) eqn:E.
  - apply existsb_exists in E. destruct E as [x [Hx Hle]].
    apply Nat.leb_le in Hle. exists x; split; auto.
    apply mem_allStrings_iff; exact Hx.
  - exfalso.
    assert (Hshort : forall x, In x (allStrings n) -> length (enc x) < n).
    { intros x Hx.
      destruct (n <=? length (enc x)) eqn:Hb.
      - assert (existsb (fun x => n <=? length (enc x)) (allStrings n) = true)
          as T by (apply existsb_exists; exists x; auto).
        rewrite T in E; discriminate.
      - apply Nat.leb_gt in Hb; exact Hb. }
    assert (Hnd : NoDup (map enc (allStrings n))).
    { apply nodup_map_of_injOn; [apply nodup_allStrings|].
      intros x y Hx Hy Hxy; apply Hinj; auto; apply mem_allStrings_iff; auto. }
    assert (Hsub : forall z, In z (map enc (allStrings n)) -> In z (shorter n)).
    { intros z Hz. apply in_map_iff in Hz. destruct Hz as [x [Hx Hin]]; subst.
      apply mem_shorter_iff, Hshort; exact Hin. }
    pose proof (pigeonhole _ _ Hnd Hsub) as Hle.
    rewrite length_map, length_allStrings, length_shorter in Hle.
    pose proof (one_le_pow2 n). lia.
Qed.

Definition collides (enc : list bool -> list bool) (x y : list bool) : bool :=
  if str_eq_dec x y then false
  else if str_eq_dec (enc x) (enc y) then true else false.

Theorem shortening_forces_collision (enc : list bool -> list bool) (n : nat) :
  (forall x : list bool, length x = n -> length (enc x) < n) ->
  exists x y : list bool, length x = n /\ length y = n /\ x <> y /\ enc x = enc y.
Proof.
  intros Hshort.
  destruct (existsb (fun x => existsb (collides enc x) (allStrings n))
              (allStrings n)) eqn:E.
  - apply existsb_exists in E. destruct E as [x [Hx E]].
    apply existsb_exists in E. destruct E as [y [Hy E]].
    unfold collides in E.
    destruct (str_eq_dec x y) as [_|Hne]; [discriminate|].
    destruct (str_eq_dec (enc x) (enc y)) as [Heq|]; [|discriminate].
    exists x, y. repeat split; auto; apply mem_allStrings_iff; auto.
  - exfalso.
    assert (Hinj : InjectiveOnLength enc n).
    { intros x y Hx Hy Hxy.
      destruct (str_eq_dec x y) as [Heq|Hne]; auto. exfalso.
      assert (existsb (fun x => existsb (collides enc x) (allStrings n))
                (allStrings n) = true) as T.
      { apply existsb_exists. exists x. split; [apply mem_allStrings_iff; auto|].
        apply existsb_exists. exists y. split; [apply mem_allStrings_iff; auto|].
        unfold collides.
        destruct (str_eq_dec x y); [contradiction|].
        destruct (str_eq_dec (enc x) (enc y)); [reflexivity|contradiction]. }
      rewrite T in E; discriminate. }
    destruct (no_universal_compression enc n Hinj) as [x [Hx Hge]].
    pose proof (Hshort x Hx). lia.
Qed.

(* Incompressible strings (Kolmogorov-style counting). *)
Definition Describable (dec : list bool -> list bool) (m : nat) (x : list bool) : Prop :=
  exists p : list bool, length p < m /\ dec p = x.

Theorem describable_iff (dec : list bool -> list bool) (m : nat) (x : list bool) :
  Describable dec m x <-> In x (map dec (shorter m)).
Proof.
  split.
  - intros [p [Hp Hx]]. apply in_map_iff. exists p; split; auto.
    apply mem_shorter_iff; exact Hp.
  - intros H. apply in_map_iff in H. destruct H as [p [Hx Hp]].
    exists p; split; auto. apply mem_shorter_iff; exact Hp.
Qed.

Definition inb (x : list bool) (L : list (list bool)) : bool :=
  if in_dec str_eq_dec x L then true else false.

Theorem count_describable_le (dec : list bool -> list bool) (n m : nat) :
  length (filter (fun x => inb x (map dec (shorter m))) (allStrings n)) <= 2 ^ m - 1.
Proof.
  assert (Hnd : NoDup (filter (fun x => inb x (map dec (shorter m))) (allStrings n))).
  { apply NoDup_filter, nodup_allStrings. }
  assert (Hsub : forall x,
            In x (filter (fun x => inb x (map dec (shorter m))) (allStrings n)) ->
            In x (map dec (shorter m))).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hb].
    unfold inb in Hb. destruct (in_dec str_eq_dec x (map dec (shorter m)));
      [assumption | discriminate]. }
  pose proof (pigeonhole _ _ Hnd Hsub) as Hle.
  rewrite length_map, length_shorter in Hle. exact Hle.
Qed.

Theorem incompressible_exists (dec : list bool -> list bool) (n : nat) :
  exists x : list bool, length x = n /\ ~ Describable dec n x.
Proof.
  destruct (existsb (fun x => negb (inb x (map dec (shorter n)))) (allStrings n)) eqn:E.
  - apply existsb_exists in E. destruct E as [x [Hx Hb]].
    exists x. split; [apply mem_allStrings_iff; exact Hx|].
    rewrite describable_iff. unfold inb in Hb.
    destruct (in_dec str_eq_dec x (map dec (shorter n))); [discriminate | assumption].
  - exfalso.
    assert (Hall : forall x, In x (allStrings n) -> In x (map dec (shorter n))).
    { intros x Hx.
      destruct (in_dec str_eq_dec x (map dec (shorter n))) as [Hin|Hnin]; auto.
      assert (existsb (fun x => negb (inb x (map dec (shorter n)))) (allStrings n) = true)
        as T.
      { apply existsb_exists. exists x. split; auto. unfold inb.
        destruct (in_dec str_eq_dec x (map dec (shorter n))); [contradiction|reflexivity]. }
      rewrite T in E; discriminate. }
    pose proof (pigeonhole _ _ (nodup_allStrings n) Hall) as Hle.
    rewrite length_map, length_allStrings, length_shorter in Hle.
    pose proof (one_le_pow2 n). lia.
Qed.

(* Compression that exploits structure. *)
Definition run (b : bool) (n : nat) : list bool := repeat b n.

Definition runCode (x : list bool) : list bool := [hd false x].

Theorem runCode_injective_on_runs (n : nat) (b c : bool) :
  1 <= n -> runCode (run b n) = runCode (run c n) -> run b n = run c n.
Proof.
  intros Hn H. destruct n as [|k]; [lia|].
  unfold runCode, run in H. simpl in H. injection H; intros; subst; reflexivity.
Qed.

Theorem runCode_length (b : bool) (n : nat) : length (runCode (run b n)) = 1.
Proof. reflexivity. Qed.
