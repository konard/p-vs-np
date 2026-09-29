(* Issue #532, Idea 05: greedy optimization.

   One decision step followed by a forced continuation. An option is a pair
   (first, rest): the visible cost and the cost it forces later. Greedy picks
   the smallest visible cost, and the optimum picks the smallest total.

   Proved for all parameters: the generic selection is correct; greedy is
   optimal when every continuation costs the same; greedy has unbounded
   approximation ratio on the trap family [(1,k); (2,0)]; greedy is exact for
   independent decisions (one element per group, a partition matroid).

   Verdict: refuted as a route (general theorem). *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(* Generic selection by a key *)

Fixpoint argminBy {A : Type} (f : A -> nat) (o : A) (os : list A) : A :=
  match os with
  | [] => o
  | p :: ps =>
      let q := argminBy f p ps in
      if f q <? f o then q else o
  end.

(* The selected element is one of the candidates. *)
Theorem argminBy_mem : forall (A : Type) (f : A -> nat) (os : list A) (o : A),
  In (argminBy f o os) (o :: os).
Proof.
  intros A f os. induction os as [|p ps IH]; intro o; simpl.
  - left; reflexivity.
  - destruct (f (argminBy f p ps) <? f o).
    + right. apply IH.
    + left; reflexivity.
Qed.

(* The selected element has the smallest key among the candidates. *)
Theorem argminBy_le : forall (A : Type) (f : A -> nat) (os : list A) (o : A) (p : A),
  In p (o :: os) -> f (argminBy f o os) <= f p.
Proof.
  intros A f os. induction os as [|q qs IH]; intros o p Hp; simpl.
  - destruct Hp as [Hp|Hp]; [subst; lia|contradiction].
  - destruct (f (argminBy f q qs) <? f o) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct Hp as [Hp|Hp].
      * subst; lia.
      * apply IH; exact Hp.
    + apply Nat.ltb_ge in Hlt.
      destruct Hp as [Hp|Hp].
      * subst; lia.
      * specialize (IH q p Hp); lia.
Qed.

(* Two-stage instances *)

Definition total (o : nat * nat) : nat := fst o + snd o.

Definition greedyChoice (o : nat * nat) (os : list (nat * nat)) : nat * nat :=
  argminBy (fun p => fst p) o os.

Definition greedyCost (o : nat * nat) (os : list (nat * nat)) : nat :=
  total (greedyChoice o os).

Definition optCost (o : nat * nat) (os : list (nat * nat)) : nat :=
  total (argminBy total o os).

Theorem optCost_le : forall o os p, In p (o :: os) -> optCost o os <= total p.
Proof. intros o os p Hp. unfold optCost. apply argminBy_le; exact Hp. Qed.

Theorem optCost_achieved : forall o os,
  exists p, In p (o :: os) /\ total p = optCost o os.
Proof.
  intros o os. exists (argminBy total o os). split.
  - apply argminBy_mem.
  - reflexivity.
Qed.

Theorem greedyChoice_mem : forall o os, In (greedyChoice o os) (o :: os).
Proof. intros o os. unfold greedyChoice. apply argminBy_mem. Qed.

Theorem optCost_le_greedyCost : forall o os, optCost o os <= greedyCost o os.
Proof. intros o os. unfold greedyCost. apply optCost_le, greedyChoice_mem. Qed.

(* If every option forces the same continuation cost c, greedy is optimal. *)
Theorem greedy_optimal_of_uniform_continuation : forall o os c,
  (forall p, In p (o :: os) -> snd p = c) ->
  greedyCost o os = optCost o os.
Proof.
  intros o os c Hc. apply Nat.le_antisymm.
  - destruct (optCost_achieved o os) as [p [Hp Hpt]].
    rewrite <- Hpt.
    pose proof (argminBy_le _ (fun q => fst q) os o p Hp) as Hle.
    pose proof (Hc _ (greedyChoice_mem o os)) as Hg.
    pose proof (Hc p Hp) as Hpc.
    unfold greedyCost, greedyChoice, total in *. simpl in Hle. lia.
  - apply optCost_le_greedyCost.
Qed.

(* The trap family *)

Theorem trap_greedyCost : forall k, greedyCost (1, k) [(2, 0)] = k + 1.
Proof. intro k. unfold greedyCost, greedyChoice, total. simpl. lia. Qed.

Theorem trap_optCost : forall k, 1 <= k -> optCost (1, k) [(2, 0)] = 2.
Proof.
  intros k Hk. unfold optCost, total. simpl.
  destruct (2 <? S k) eqn:E; simpl.
  - reflexivity.
  - apply Nat.ltb_ge in E. lia.
Qed.

(* Greedy has unbounded approximation ratio. *)
Theorem greedy_ratio_unbounded : forall r,
  exists o os, 0 < optCost o os /\ r * optCost o os < greedyCost o os.
Proof.
  intro r. exists (1, 2 * r + 1), [(2, 0)].
  rewrite (trap_optCost (2 * r + 1)) by lia.
  rewrite trap_greedyCost. lia.
Qed.

(* Independent decisions: greedy is exact *)

Inductive Picks : list (nat * list nat) -> list nat -> Prop :=
  | Picks_nil : Picks [] []
  | Picks_cons : forall h t gs xs x,
      In x (h :: t) -> Picks gs xs -> Picks ((h, t) :: gs) (x :: xs).

Fixpoint greedyPicks (gs : list (nat * list nat)) : list nat :=
  match gs with
  | [] => []
  | (h, t) :: gs' => argminBy (fun x => x) h t :: greedyPicks gs'
  end.

Fixpoint sumList (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + sumList xs'
  end.

Theorem greedyPicks_valid : forall gs, Picks gs (greedyPicks gs).
Proof.
  induction gs as [|[h t] gs IH]; simpl.
  - constructor.
  - constructor; [apply argminBy_mem|exact IH].
Qed.

Theorem greedyPicks_optimal : forall gs xs,
  Picks gs xs -> sumList (greedyPicks gs) <= sumList xs.
Proof.
  intros gs xs Hp. induction Hp as [|h t gs xs x Hx Hp IH]; simpl.
  - lia.
  - pose proof (argminBy_le _ (fun y => y) t h x Hx) as Hle. simpl in Hle. lia.
Qed.
