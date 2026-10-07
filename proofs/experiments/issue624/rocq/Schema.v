From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue624.rocq Require Import
  LocalCNF MachineCNF SuccessorCNF RunCNF InitialCNF CertificateCNF VerifierTableau FixedWindow.
Import ListNotations.

(** Generated schema syntax and data: run generate_schema.py. Products support
    row strides; literal ranges support long clauses. Uses the existing CNF. *)
Module Schema.
Import Complexity Machines LocalCNF MachineCNF SuccessorCNF RunCNF InitialCNF.
Import CertificateCNF VerifierTableau FixedWindow.

Inductive Expr :=
| EConst (value : nat) | EParam (slot : nat) | EIdx (slot : nat)
| EBit (position : Expr)
| EAdd (a b : Expr) | EMul (a b : Expr) | ESub (a b : Expr)
| ESelectEq (a b yes no : Expr).
Definition setIndex (indices : nat -> nat) (slot value : nat) :=
  fun k => if Nat.eqb k slot then value else indices k.
Fixpoint evalExpr (e : Expr) (params : list nat) (x : Word) (indices : nat -> nat) : nat :=
  match e with
  | EConst n => n | EParam k => nth k params 0 | EIdx k => indices k
  | EBit e => if nth (evalExpr e params x indices) x false then 1 else 0
  | EAdd a b => evalExpr a params x indices + evalExpr b params x indices
  | EMul a b => evalExpr a params x indices * evalExpr b params x indices
  | ESub a b => evalExpr a params x indices - evalExpr b params x indices
  | ESelectEq a b yes no => if Nat.eqb (evalExpr a params x indices) (evalExpr b params x indices)
      then evalExpr yes params x indices else evalExpr no params x indices
  end.
Inductive Literals :=
| LList (values : list (Expr * bool)) | LAppend (a b : Literals)
| LRange (slot : nat) (count value : Expr) (pos : bool).
Fixpoint evalLiterals (ls : Literals) (params : list nat) (x : Word) (indices : nat -> nat) : Clause :=
  match ls with
  | LList vs => map (fun ep => mkLit (evalExpr (fst ep) params x indices) (snd ep)) vs
  | LAppend a b => evalLiterals a params x indices ++ evalLiterals b params x indices
  | LRange slot count value pos => map
      (fun i => mkLit (evalExpr value params x (setIndex indices slot i)) pos)
      (seq 0 (evalExpr count params x indices))
  end.
Inductive Schema :=
| SEmpty | SClause (values : Literals) | SSeq (a b : Schema)
| SForRange (slot : nat) (count : Expr) (body : Schema)
| SIfLt (a b : Expr) (yes no : Schema)
| SGuard (guards : Literals) (body : Schema).
Fixpoint evalSchema (s : Schema) (params : list nat) (x : Word) (indices : nat -> nat) : CNF :=
  match s with
  | SEmpty => [] | SClause vs => [evalLiterals vs params x indices]
  | SSeq a b => evalSchema a params x indices ++ evalSchema b params x indices
  | SForRange slot count body => flat_map
      (fun i => evalSchema body params x (setIndex indices slot i))
      (seq 0 (evalExpr count params x indices))
  | SIfLt a b yes no => if Nat.ltb (evalExpr a params x indices) (evalExpr b params x indices)
      then evalSchema yes params x indices else evalSchema no params x indices
  | SGuard guards body => map (fun c => evalLiterals guards params x indices ++ c)
      (evalSchema body params x indices)
  end.
Definition seqSchemas (ss : list Schema) : Schema := fold_right SSeq SEmpty ss.

Definition oneHotSchema (d : nat) (base : Expr) (size : Expr) : Schema :=
  (SSeq (SClause (LRange d size (EAdd base (EIdx d)) true)) (SForRange d size (SForRange (d + 1) (ESub (ESub size (EIdx d)) (EConst 1)) (SClause (LList [((EAdd base (EIdx d)), false); ((EAdd (EAdd base (EConst 1)) (EAdd (EIdx d) (EIdx (d + 1)))), false)]))))).

Definition certificateSchema (d : nat) (start : Expr) (bound : Expr) : Schema :=
  (SSeq (SForRange d bound (SSeq (SClause (LList [((EAdd (EMul (EConst 2) (EAdd start (EIdx d))) (EConst 1)), false); ((EMul (EConst 2) (EAdd start (EIdx d))), true)])) (SClause (LList [((EMul (EConst 2) (EAdd (EAdd start (EIdx d)) (EConst 1))), false); ((EMul (EConst 2) (EAdd start (EIdx d))), true)])))) (SClause (LList [((EMul (EConst 2) (EAdd start bound)), false)]))).

Definition rowSchema (d : nat) (base : Expr) (states : Expr) (width : Expr) : Schema :=
  (SSeq (oneHotSchema d base states) (SSeq (oneHotSchema d (EAdd base states) width) (SForRange d width (oneHotSchema (d + 1) (EAdd (EAdd (EAdd base states) width) (EMul (EConst 4) (EIdx d))) (EConst 4))))).

Definition guardLiterals (base : Expr) (states : Expr) (width : Expr) (q : nat) (head : Expr) (symbol : nat) : Literals :=
  (LList [((EAdd base (EConst q)), false); ((EAdd (EAdd base states) head), false); ((EAdd (EAdd (EAdd (EAdd base states) width) (EMul (EConst 4) head)) (EConst symbol)), false)]).

Definition copySchema (d : nat) (prem : Literals) (base : Expr) (next : Expr) (states : Expr) (width : Expr) (head : Expr) (write : nat) : Schema :=
  (SForRange d width (SForRange (d + 1) (EConst 4) (SGuard prem (SClause (LList [((EAdd (EAdd (EAdd (EAdd base states) width) (EMul (EConst 4) (EIdx d))) (EIdx (d + 1))), false); ((EAdd (EAdd (EAdd (EAdd next states) width) (EMul (EConst 4) (EIdx d))) (ESelectEq (EIdx d) head (EConst write) (EIdx (d + 1)))), true)]))))).

Definition sourceSchema (base : Expr) (position : Expr) : Schema :=
  (SSeq (SClause (LList [((EMul (EConst 2) position), true); (base, true)])) (SSeq (SClause (LList [((EMul (EConst 2) position), false); ((EAdd (EMul (EConst 2) position) (EConst 1)), true); ((EAdd base (EConst 1)), true)])) (SClause (LList [((EMul (EConst 2) position), false); ((EAdd (EMul (EConst 2) position) (EConst 1)), false); ((EAdd base (EConst 2)), true)])))).

Definition instructionSchema (d : nat) (m : Machine) (base : Expr) (next : Expr) (width : Expr) (q : nat) (head : Expr) (symbol : nat) : Schema :=
  (match instruction m q (symbolOfIndex symbol) with | halt _ => (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SClause (LList []))) | move target write dir => (if Nat.ltb target (length (program m)) then (match dir with | left => (SIfLt (EConst 0) head (SSeq (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SSeq (SClause (LList [((EAdd next (EConst target)), true)])) (SClause (LList [((EAdd (EAdd next (EConst (length (program m)))) (match dir with | left => (ESub head (EConst 1)) | right => (EAdd head (EConst 1)) | stay => head end)), true)])))) (copySchema d (guardLiterals base (EConst (length (program m))) width q head symbol) base next (EConst (length (program m))) width head (symbolIndex write))) (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SClause (LList [])))) | right => (SIfLt (EAdd head (EConst 1)) width (SSeq (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SSeq (SClause (LList [((EAdd next (EConst target)), true)])) (SClause (LList [((EAdd (EAdd next (EConst (length (program m)))) (match dir with | left => (ESub head (EConst 1)) | right => (EAdd head (EConst 1)) | stay => head end)), true)])))) (copySchema d (guardLiterals base (EConst (length (program m))) width q head symbol) base next (EConst (length (program m))) width head (symbolIndex write))) (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SClause (LList [])))) | stay => (SSeq (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SSeq (SClause (LList [((EAdd next (EConst target)), true)])) (SClause (LList [((EAdd (EAdd next (EConst (length (program m)))) (match dir with | left => (ESub head (EConst 1)) | right => (EAdd head (EConst 1)) | stay => head end)), true)])))) (copySchema d (guardLiterals base (EConst (length (program m))) width q head symbol) base next (EConst (length (program m))) width head (symbolIndex write))) end) else (SGuard (guardLiterals base (EConst (length (program m))) width q head symbol) (SClause (LList [])))) end).

Definition transitionSchema (d : nat) (m : Machine) (base : Expr) (next : Expr) (width : Expr) : Schema :=
  (seqSchemas (map (fun q => (SForRange d width (seqSchemas (map (fun symbol => (instructionSchema (d + 1) m base next width q (EIdx d) symbol)) (seq 0 4))))) (seq 0 (length (program m))))).

Definition haltSchema (d : nat) (m : Machine) (base : Expr) (width : Expr) : Schema :=
  (seqSchemas (map (fun q => (SForRange d width (seqSchemas (map (fun symbol => (match instruction m q (symbolOfIndex symbol) with | halt true => (SEmpty) | _ => (SGuard (guardLiterals base (EConst (length (program m))) width q (EIdx d) symbol) (SClause (LList []))) end)) (seq 0 4))))) (seq 0 (length (program m))))).

Definition successorSchema (d : nat) (m : Machine) (base : Expr) (next : Expr) (width : Expr) : Schema :=
  (SSeq (rowSchema d base (EConst (length (program m))) width) (SSeq (rowSchema d next (EConst (length (program m))) width) (transitionSchema d m base next width))).

Definition stopLiterals (d : nat) (base : Expr) (states : Expr) (width : Expr) (count : Expr) : Literals :=
  (LRange d count (EAdd (EAdd base (EMul (EAdd (EAdd states (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) (EAdd states (EMul (EConst 5) width))) true).

Definition runSchema (d : nat) (m : Machine) (base : Expr) (width : Expr) (fuel : Expr) : Schema :=
  (SSeq (SForRange d fuel (SGuard (stopLiterals (d + 1) base (EConst (length (program m))) width (EIdx d)) (SSeq (rowSchema (d + 1) (EAdd base (EMul (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) (EConst (length (program m))) width) (SSeq (SGuard (LList [((EAdd (EAdd base (EMul (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) (EAdd (EConst (length (program m))) (EMul (EConst 5) width))), false)]) (haltSchema (d + 1) m (EAdd base (EMul (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) width)) (SGuard (LList [((EAdd (EAdd base (EMul (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) (EAdd (EConst (length (program m))) (EMul (EConst 5) width))), true)]) (successorSchema (d + 1) m (EAdd base (EMul (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) (EAdd (EAdd base (EMul (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)) (EIdx d))) (EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1))) width)))))) (SClause (stopLiterals d base (EConst (length (program m))) width fuel))).

Definition initialSchema (m : Machine) (paired : bool) : Schema :=
  (SSeq (rowSchema 0 (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m))) (EParam 3)) (SSeq (SClause (LList [((EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)), true)])) (SSeq (SClause (LList [((EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 2)), true)])) (SSeq (SForRange 0 (EParam 2) (SClause (LList [((EAdd (EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 3)) (EMul (EConst 4) (EAdd (EConst 0) (EIdx 0)))), true)]))) (SSeq (SForRange 0 (EParam 0) (SClause (LList [((EAdd (EAdd (EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 3)) (EMul (EConst 4) (EAdd (EParam 2) (EIdx 0)))) (EAdd (EBit (EIdx 0)) (EConst 1))), true)]))) (if paired then (SSeq (SClause (LList [((EAdd (EAdd (EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 3)) (EMul (EConst 4) (EAdd (EParam 2) (EParam 0)))) (EConst 3)), true)])) (SSeq (SForRange 0 (EParam 1) (sourceSchema (EAdd (EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 3)) (EMul (EConst 4) (EAdd (EAdd (EAdd (EParam 2) (EParam 0)) (EConst 1)) (EIdx 0)))) (EIdx 0))) (SForRange 0 (ESub (ESub (ESub (ESub (EParam 3) (EParam 2)) (EParam 0)) (EConst 1)) (EParam 1)) (SClause (LList [((EAdd (EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 3)) (EMul (EConst 4) (EAdd (EAdd (EAdd (EAdd (EParam 2) (EParam 0)) (EConst 1)) (EParam 1)) (EIdx 0)))), true)]))))) else (SForRange 0 (ESub (ESub (EParam 3) (EParam 2)) (EParam 0)) (SClause (LList [((EAdd (EAdd (EAdd (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EConst (length (program m)))) (EParam 3)) (EMul (EConst 4) (EAdd (EAdd (EParam 2) (EParam 0)) (EIdx 0)))), true)]))))))))).

Definition machineSchema (m : Machine) (paired : bool) : Schema :=
  (SSeq (certificateSchema 0 (EConst 0) (EParam 1)) (SSeq (initialSchema m paired) (runSchema 0 m (EAdd (EMul (EConst 2) (EParam 1)) (EConst 1)) (EParam 3) (EParam 2)))).

Definition tableauSchema (np : ClassNP) : Schema :=
  (match np_verifier np with | ignoreCertificate m => (machineSchema m false) | paired m => (machineSchema m true) end).

Definition tableauParams (np : ClassNP) (n : nat) : list nat :=
  [n; evalPoly (np_certBound np) n; maxClock np n; windowWidth np n].

(* END GENERATED SCHEMA DATA *)

Fixpoint Closed (depth : nat) (e : Expr) : Prop :=
  match e with
  | EConst _ | EParam _ => True
  | EIdx k => k < depth
  | EBit e => Closed depth e
  | EAdd a b | EMul a b | ESub a b => Closed depth a /\ Closed depth b
  | ESelectEq a b y n => Closed depth a /\ Closed depth b /\ Closed depth y /\ Closed depth n
  end.
Theorem setIndex_same : forall env d i, setIndex env d i d = i.
Proof. intros; unfold setIndex; rewrite Nat.eqb_refl; reflexivity. Qed.
Theorem setIndex_other : forall env d i k, k <> d -> setIndex env d i k = env k.
Proof. intros; unfold setIndex; destruct (Nat.eqb_spec k d); congruence. Qed.
Theorem closed_mono : forall e d k, Closed d e -> d <= k -> Closed k e.
Proof. induction e; simpl; intros; intuition (eauto; lia). Qed.
Theorem evalExpr_setIndex : forall e p x env d i, Closed d e ->
  evalExpr e p x (setIndex env d i) = evalExpr e p x env.
Proof.
  induction e; intros p x env d i h; simpl in *; try reflexivity.
  - apply setIndex_other; lia.
  - rewrite IHe by assumption; reflexivity.
  - destruct h; rewrite IHe1, IHe2 by assumption; reflexivity.
  - destruct h; rewrite IHe1, IHe2 by assumption; reflexivity.
  - destruct h; rewrite IHe1, IHe2 by assumption; reflexivity.
  - destruct h as [ha [hb [hy hn]]]. rewrite IHe1, IHe2, IHe3, IHe4 by assumption; reflexivity.
Qed.
Theorem flatMap_congr : forall (A B : Type) (xs : list A) (f g : A -> list B),
  (forall a, In a xs -> f a = g a) -> flat_map f xs = flat_map g xs.
Proof. intros A B xs; induction xs; intros; simpl; [reflexivity|]. rewrite H by (left; reflexivity). f_equal; apply IHxs. intros; apply H; right; assumption. Qed.
Theorem flatMap_map : forall (A B C : Type) (xs : list A) (f : A -> B) (g : B -> list C),
  flat_map g (map f xs) = flat_map (fun a => g (f a)) xs.
Proof. intros A B C xs; induction xs; intros; simpl; [reflexivity|]. rewrite IHxs; reflexivity. Qed.
Theorem map_eq_flatMap : forall (A B : Type) (xs : list A) (f : A -> B),
  map f xs = flat_map (fun a => [f a]) xs.
Proof. intros A B xs; induction xs; intros; simpl; [reflexivity|]. rewrite IHxs; reflexivity. Qed.
Theorem flatMap_range_succ : forall (A : Type) n (f : nat -> list A),
  flat_map f (seq 0 (n+1)) = f 0 ++ flat_map (fun i => f (i+1)) (seq 0 n).
Proof.
  intros. replace (n+1) with (S n) by lia; simpl seq.
  rewrite <- (seq_shift n 0). simpl flat_map. rewrite flatMap_map; simpl. f_equal.
  apply flatMap_congr; intros; f_equal; lia.
Qed.
Theorem map_range_succ : forall (A : Type) n (f : nat -> A),
  map f (seq 0 (n+1)) = f 0 :: map (fun i => f (i+1)) (seq 0 n).
Proof.
  intros. replace (n+1) with (S n) by lia; simpl seq.
  rewrite <- (seq_shift n 0). simpl map. rewrite map_map; simpl. f_equal.
  apply map_ext; intros; f_equal; lia.
Qed.
Theorem atMostOne_range : forall base size,
  atMostOne base size = flat_map (fun i =>
    map (fun j => [mkLit (base+i) false; mkLit (base+1+(i+j)) false])
      (seq 0 (size-i-1))) (seq 0 size).
Proof.
  intros base size; revert base; induction size as [|n IH]; intro base; [reflexivity|].
  replace (S n) with (n+1) by lia. rewrite flatMap_range_succ. replace (n+1) with (S n) by lia. simpl atMostOne.
  rewrite IH. simpl Nat.add. replace (S n-0-1) with n by lia. rewrite Nat.add_0_r. f_equal.
  apply flatMap_congr; intros i hi. replace (S n-(i+1)-1) with (n-i-1) by lia.
  apply map_ext; intro j. repeat (f_equal; try lia).
Qed.
Theorem oneHotSchema_eq : forall d base size p x env,
  Closed d base -> Closed d size ->
  evalSchema (oneHotSchema d base size) p x env =
    oneHot (evalExpr base p x env) (evalExpr size p x env).
Proof.
  intros d base size p x env hb hs. unfold oneHotSchema; simpl evalSchema; simpl evalLiterals; simpl evalExpr.
  unfold oneHot; rewrite atMostOne_range. simpl app. f_equal.
  - apply map_ext; intro i; simpl. rewrite evalExpr_setIndex by assumption.
    rewrite setIndex_same; reflexivity.
  - apply flatMap_congr; intros i hi. simpl evalExpr.
    rewrite evalExpr_setIndex by assumption; rewrite setIndex_same.
    rewrite <- map_eq_flatMap.
    apply map_ext; intro j; simpl.
    rewrite evalExpr_setIndex by (apply closed_mono with d; [assumption|lia]).
    rewrite evalExpr_setIndex by assumption.
    rewrite setIndex_same, setIndex_other by lia. rewrite !setIndex_same. repeat (f_equal; try lia).
Qed.

Theorem certificateCNF_range : forall start bound,
  certificateCNF start bound = flat_map (fun i =>
    [[mkLit (2*(start+i)+1) false; mkLit (2*(start+i)) true];
     [mkLit (2*(start+i+1)) false; mkLit (2*(start+i)) true]]) (seq 0 bound) ++
    [[mkLit (2*(start+bound)) false]].
Proof.
  intros start bound; revert start; induction bound as [|n IH]; intro start.
  - simpl. rewrite !Nat.add_0_r. reflexivity.
  - replace (S n) with (n+1) by lia. rewrite flatMap_range_succ.
    replace (n+1) with (S n) by lia. cbn [certificateCNF]. rewrite IH.
    simpl app. cbn [Nat.mul]. rewrite !Nat.add_0_r. f_equal. f_equal. f_equal.
    + apply flatMap_congr; intros i hi. repeat (f_equal; try lia).
    + repeat (f_equal; try lia).
Qed.
Theorem certificateSchema_eq : forall d start bound p x env,
  Closed d start -> Closed d bound ->
  evalSchema (certificateSchema d start bound) p x env =
    certificateCNF (evalExpr start p x env) (evalExpr bound p x env).
Proof.
  intros d start bound p x env hs hb. unfold certificateSchema.
  cbn [evalSchema evalLiterals evalExpr map fst snd]. rewrite certificateCNF_range.
  f_equal.
  - apply flatMap_congr; intros i hi. rewrite !evalExpr_setIndex by assumption.
    rewrite !setIndex_same. reflexivity.
Qed.
Theorem evalSeqSchemas : forall ss p x env,
  evalSchema (seqSchemas ss) p x env = flat_map (fun s => evalSchema s p x env) ss.
Proof. induction ss; intros; cbn [seqSchemas evalSchema flat_map fold_right]; [reflexivity|rewrite IHss; reflexivity]. Qed.
Theorem rowSchema_eq : forall d base states width p x env,
  Closed d base -> Closed d states -> Closed d width ->
  evalSchema (rowSchema d base states width) p x env =
    rowCNF (evalExpr base p x env) (evalExpr states p x env) (evalExpr width p x env).
Proof.
  intros d base states width p x env hb hs hw.
  unfold rowSchema. cbn [evalSchema].
  rewrite !oneHotSchema_eq by (simpl; auto).
  cbn [evalExpr]. unfold rowCNF. rewrite <- app_assoc. f_equal. f_equal.
  apply flatMap_congr; intros i hi.
  rewrite oneHotSchema_eq by (simpl; repeat split; try lia; eapply closed_mono; eauto; lia).
  cbn [evalExpr]. rewrite !evalExpr_setIndex by assumption.
  rewrite setIndex_same. reflexivity.
Qed.
Fixpoint LiteralsClosed (depth : nat) (ls : Literals) : Prop :=
  match ls with
  | LList vs => forall v, In v vs -> Closed depth (fst v)
  | LAppend a b => LiteralsClosed depth a /\ LiteralsClosed depth b
  | LRange _ _ _ _ => False
  end.
Theorem literals_closed_mono : forall vs d k,
  LiteralsClosed d vs -> d <= k -> LiteralsClosed k vs.
Proof. induction vs; simpl; intros; [intros; eapply closed_mono; eauto|intuition eauto|contradiction]. Qed.
Theorem evalLiterals_setIndex : forall vs p x env d i,
  LiteralsClosed d vs -> evalLiterals vs p x (setIndex env d i) = evalLiterals vs p x env.
Proof.
  induction vs; intros p x env d i h; simpl in *.
  - apply map_ext_in; intros [e b] he; simpl. rewrite evalExpr_setIndex by (apply (h (e,b)); assumption). reflexivity.
  - destruct h; rewrite IHvs1, IHvs2 by assumption; reflexivity.
  - contradiction.
Qed.
Theorem guardLiterals_eq : forall base states width q head symbol p x env,
  evalLiterals (guardLiterals base states width q head symbol) p x env =
    map negate (guard (evalExpr base p x env) (evalExpr states p x env)
      (evalExpr width p x env) q (evalExpr head p x env) symbol).
Proof. reflexivity. Qed.
Theorem guardLiterals_closed : forall base states width head q symbol d,
  Closed d base -> Closed d states -> Closed d width -> Closed d head ->
  LiteralsClosed d (guardLiterals base states width q head symbol).
Proof.
  intros. unfold guardLiterals. simpl. intros v [he|[he|[he|[]]]]; subst v; simpl; intuition.
Qed.
Theorem copySchema_eq : forall d prem base next states width head write p x env,
  LiteralsClosed d prem -> Closed d base -> Closed d next -> Closed d states ->
  Closed d width -> Closed d head ->
  evalSchema (copySchema d prem base next states width head write) p x env =
    flat_map (fun i => map (fun s => evalLiterals prem p x env ++
      [mkLit (tapeVar (evalExpr base p x env) (evalExpr states p x env) (evalExpr width p x env) i s) false;
       mkLit (tapeVar (evalExpr next p x env) (evalExpr states p x env) (evalExpr width p x env) i
         (if Nat.eqb i (evalExpr head p x env) then write else s)) true]) (seq 0 4))
      (seq 0 (evalExpr width p x env)).
Proof.
  intros d prem base next states width head write p x env hp hb hn hs hw hh.
  unfold copySchema. cbn [evalSchema evalExpr map].
  apply flatMap_congr; intros i hi. rewrite <- map_eq_flatMap.
  apply map_ext; intro j. cbn [evalLiterals evalExpr map fst snd].
  rewrite evalLiterals_setIndex by (eapply literals_closed_mono; eauto; lia).
  rewrite evalLiterals_setIndex by assumption.
  rewrite !evalExpr_setIndex by (eapply closed_mono; eauto; lia).
  rewrite !setIndex_same, setIndex_other by lia. rewrite !setIndex_same. reflexivity.
Qed.
Theorem sourceSchema_eq : forall base position p x env,
  evalSchema (sourceSchema base position) p x env =
    sourceCNF (evalExpr base p x env) (certificate (evalExpr position p x env)).
Proof.
  intros. unfold sourceSchema, sourceCNF, implies, negate.
  cbn [evalSchema evalLiterals evalExpr map app fst snd]. reflexivity.
Qed.

Theorem copyGuardSchema_eq : forall d base next width head m q symbol write p x env,
  Closed d base -> Closed d next -> Closed d width -> Closed d head ->
  evalSchema (copySchema d (guardLiterals base (EConst (length (program m))) width q head symbol)
    base next (EConst (length (program m))) width head (symbolIndex write)) p x env =
  copyRules (guard (evalExpr base p x env) (length (program m)) (evalExpr width p x env)
    q (evalExpr head p x env) symbol) (evalExpr base p x env) (evalExpr next p x env)
    (length (program m)) (evalExpr width p x env) (evalExpr head p x env) write.
Proof.
  intros d base next width head m q symbol write p x env hb hn hw hh.
  rewrite copySchema_eq by (try apply guardLiterals_closed; simpl; assumption || exact I).
  rewrite guardLiterals_eq. cbn [evalExpr]. unfold copyRules.
  apply flatMap_congr; intros i hi. apply map_ext; intro j.
  unfold implies. rewrite map_app. cbn [map negate var pos app].
  destruct (Nat.eqb_spec i (evalExpr head p x env)), (Nat.eq_dec i (evalExpr head p x env));
    try congruence; reflexivity.
Qed.
Theorem instructionSchema_eq : forall d m base next width q head symbol p x env,
  Closed d base -> Closed d next -> Closed d width -> Closed d head ->
  evalSchema (instructionSchema d m base next width q head symbol) p x env =
    instructionRules m (evalExpr base p x env) (evalExpr next p x env)
      (evalExpr width p x env) q (evalExpr head p x env) symbol.
Proof.
  intros d m base next width q head symbol p x env hb hn hw hh.
  pose proof (copyGuardSchema_eq d base next width head m q symbol) as hc.
  unfold instructionSchema, instructionRules.
  destruct (instruction m q (symbolOfIndex symbol)) as [b|target write dir] eqn:hi.
  - cbn [evalSchema]. rewrite guardLiterals_eq. unfold implies. rewrite app_nil_r. reflexivity.
  - specialize (hc write p x env hb hn hw hh).
    destruct dir; cbn [evalSchema evalExpr nextHead];
      destruct (Nat.ltb_spec target (length (program m)));
      cbn [evalSchema evalExpr];
      try destruct (Nat.ltb_spec 0 (evalExpr head p x env));
      try destruct (Nat.ltb_spec (evalExpr head p x env+1) (evalExpr width p x env));
      cbn [evalSchema evalExpr];
      destruct (moveAllowed_dec (length (program m)) (evalExpr width p x env)
        target (evalExpr head p x env) _) as [ha|ha];
      unfold Inside in ha; try (exfalso; intuition lia);
      rewrite ?hc; cbn [evalLiterals evalExpr map fst snd];
      rewrite ?guardLiterals_eq; unfold implies; rewrite ?app_nil_r; reflexivity.
Qed.

Theorem transitionSchema_eq : forall d m base next width p x env,
  Closed d base -> Closed d next -> Closed d width ->
  evalSchema (transitionSchema d m base next width) p x env =
    transitionCNF m (evalExpr base p x env) (evalExpr next p x env) (evalExpr width p x env).
Proof.
  intros d m base next width p x env hb hn hw.
  unfold transitionSchema, transitionCNF. rewrite evalSeqSchemas, flatMap_map.
  apply flatMap_congr; intros q hq. cbn [evalSchema evalExpr].
  apply flatMap_congr; intros h hh. rewrite evalSeqSchemas, flatMap_map.
  apply flatMap_congr; intros symbol hs.
  rewrite instructionSchema_eq by (simpl; try lia; eapply closed_mono; eauto; lia).
  cbn [evalExpr]. rewrite !evalExpr_setIndex by assumption. rewrite setIndex_same. reflexivity.
Qed.
Theorem haltSchema_eq : forall d m base width p x env,
  Closed d base -> Closed d width ->
  evalSchema (haltSchema d m base width) p x env =
    haltCNF m (evalExpr base p x env) (evalExpr width p x env).
Proof.
  intros d m base width p x env hb hw.
  unfold haltSchema, haltCNF. rewrite evalSeqSchemas, flatMap_map.
  apply flatMap_congr; intros q hq. cbn [evalSchema evalExpr].
  apply flatMap_congr; intros h hh. rewrite evalSeqSchemas, flatMap_map.
  apply flatMap_congr; intros symbol hs.
  unfold haltRule. destruct (instruction m q (symbolOfIndex symbol)) as [[|]|target write dir];
    cbn [evalSchema]; try reflexivity;
    rewrite guardLiterals_eq; cbn [evalExpr]; rewrite !evalExpr_setIndex by assumption;
    rewrite setIndex_same; unfold implies; rewrite app_nil_r; reflexivity.
Qed.
Theorem successorSchema_eq : forall d m base next width p x env,
  Closed d base -> Closed d next -> Closed d width ->
  evalSchema (successorSchema d m base next width) p x env =
    successorCNF m (evalExpr base p x env) (evalExpr next p x env) (evalExpr width p x env).
Proof.
  intros. unfold successorSchema. cbn [evalSchema].
  rewrite !rowSchema_eq, transitionSchema_eq by (simpl; auto).
  cbn [evalExpr]. unfold successorCNF. rewrite app_assoc. reflexivity.
Qed.

Theorem map_flatMap : forall (A B C : Type) (xs : list A) (f : A -> list B) (g : B -> C),
  map g (flat_map f xs) = flat_map (fun a => map g (f a)) xs.
Proof. intros A B C xs; induction xs; intros; simpl; [reflexivity|rewrite map_app, IHxs; reflexivity]. Qed.
Theorem implies_singleton : forall l, implies [l] = fun c => negate l :: c.
Proof. reflexivity. Qed.
Definition runBlock (m : Machine) (base width : nat) : CNF :=
  (rowCNF base (length (program m)) width ++
    guarded (mkLit (stopVar base (length (program m)) width) true) (haltCNF m base width)) ++
    guarded (mkLit (stopVar base (length (program m)) width) false)
      (successorCNF m base (nextBase base (length (program m)) width) width).
Definition stopPrefix (m : Machine) (base width count : nat) : Clause :=
  map (fun i => mkLit (stopVar (base + stride (length (program m)) width * i)
    (length (program m)) width) true) (seq 0 count).
Theorem stopPrefix_zero : forall m base width, stopPrefix m base width 0 = [].
Proof. reflexivity. Qed.
Theorem stopPrefix_succ : forall m base width n,
  stopPrefix m base width (n+1) = mkLit (stopVar base (length (program m)) width) true ::
    stopPrefix m (nextBase base (length (program m)) width) width n.
Proof.
  intros. unfold stopPrefix. rewrite map_range_succ. rewrite Nat.mul_0_r, Nat.add_0_r. f_equal.
  apply map_ext; intro i. unfold nextBase, stopVar. f_equal; nia.
Qed.
Theorem runCNF_range : forall m base width fuel,
  runCNF m base width fuel = flat_map (fun j =>
    map (fun c => stopPrefix m base width j ++ c)
      (runBlock m (base + stride (length (program m)) width * j) width)) (seq 0 fuel) ++
    [stopPrefix m base width fuel].
Proof.
  intros m base width fuel; revert base; induction fuel as [|n IH]; intro base.
  - reflexivity.
  - replace (S n) with (n+1) by lia. rewrite flatMap_range_succ, stopPrefix_succ.
    replace (n+1) with (S n) by lia. cbn [runCNF]. rewrite IH.
    rewrite Nat.mul_0_r, Nat.add_0_r. cbn [stopPrefix seq map app].
    assert (he : forall j, base + stride (length (program m)) width * (j+1) =
      nextBase base (length (program m)) width + stride (length (program m)) width * j).
    { intro j. unfold nextBase; nia. }
    unfold runBlock, guarded. rewrite !implies_singleton.
    cbn [negate var pos]. rewrite !map_app, !map_flatMap, !map_map.
    cbn [map app negate var pos]. rewrite ?map_id. rewrite <- !app_assoc.
    f_equal. f_equal. f_equal. f_equal.
    apply flatMap_congr; intros j hj. rewrite he, stopPrefix_succ.
    cbn [app]. rewrite !map_app, !map_map. reflexivity.
Qed.
Theorem stopLiterals_eq : forall d base width count m p x env,
  Closed d base -> Closed d width ->
  evalLiterals (stopLiterals d base (EConst (length (program m))) width count) p x env =
    stopPrefix m (evalExpr base p x env) (evalExpr width p x env) (evalExpr count p x env).
Proof.
  intros d base width count m p x env hb hw. unfold stopLiterals, stopPrefix.
  cbn [evalLiterals evalExpr]. apply map_ext; intro i.
  rewrite !evalExpr_setIndex by assumption. rewrite setIndex_same.
  unfold stopVar, stride. f_equal; lia.
Qed.

Theorem runSchema_eq : forall d m base width fuel p x env,
  Closed d base -> Closed d width ->
  evalSchema (runSchema d m base width fuel) p x env =
    runCNF m (evalExpr base p x env) (evalExpr width p x env) (evalExpr fuel p x env).
Proof.
  intros d m base width fuel p x env hb hw.
  set (str := EAdd (EAdd (EConst (length (program m))) (EMul (EConst 5) width)) (EConst 1)).
  set (row := EAdd base (EMul str (EIdx d))).
  set (next := EAdd row str).
  assert (hb' : Closed (d+1) base) by (eapply closed_mono; eauto; lia).
  assert (hw' : Closed (d+1) width) by (eapply closed_mono; eauto; lia).
  assert (hstr : Closed (d+1) str) by (unfold str; simpl; intuition).
  assert (hrow : Closed (d+1) row) by (unfold row; simpl; intuition lia).
  assert (hnext : Closed (d+1) next) by (unfold next; simpl; auto).
  unfold runSchema. cbn [evalSchema].
  rewrite stopLiterals_eq by assumption. rewrite runCNF_range. f_equal.
  apply flatMap_congr; intros j hj.
  fold str row next.
  cbn [evalSchema]. rewrite rowSchema_eq, haltSchema_eq, successorSchema_eq, stopLiterals_eq
    by (simpl; auto).
  cbn [evalLiterals evalExpr map fst snd].
  unfold next, row, str. cbn [evalExpr]. rewrite !evalExpr_setIndex by assumption.
  rewrite setIndex_same. unfold runBlock, guarded. rewrite !implies_singleton.
  cbn [negate var pos]. rewrite !map_app, !map_map.
  unfold nextBase, stopVar, stride. cbn [negate var pos app].
  rewrite <- !app_assoc. rewrite !Nat.add_assoc. reflexivity.
Qed.
Theorem tapeCNF_append : forall base xs ys,
  tapeCNF base (xs++ys) = tapeCNF base xs ++ tapeCNF (base+4*length xs) ys.
Proof.
  intros base xs; revert base; induction xs; intros; cbn [tapeCNF app length].
  - rewrite Nat.mul_0_r, Nat.add_0_r; reflexivity.
  - rewrite IHxs, app_assoc. replace (base+4* S (length xs)) with (base+4+4*length xs) by lia. reflexivity.
Qed.
Theorem tapeCNF_map_range : forall base count (f : nat -> Source),
  tapeCNF base (map f (seq 0 count)) = flat_map (fun i => sourceCNF (base+4*i) (f i)) (seq 0 count).
Proof.
  intros base count; revert base; induction count as [|n IH]; intros base f; [reflexivity|].
  replace (S n) with (n+1) by lia. rewrite map_range_succ, flatMap_range_succ.
  cbn [tapeCNF]. rewrite IH. rewrite Nat.mul_0_r, Nat.add_0_r. f_equal.
  apply flatMap_congr; intros i hi. f_equal; lia.
Qed.
Theorem tapeCNF_blank : forall base count,
  tapeCNF base (repeat (fixed blank) count) =
    map (fun i => [mkLit (base+4*i) true]) (seq 0 count).
Proof.
  intros. assert (hr : repeat (fixed blank) count = map (fun _ : nat => fixed blank) (seq 0 count)).
  { rewrite map_const, length_seq; reflexivity. }
  rewrite hr, tapeCNF_map_range. cbn [sourceCNF symbolIndex]. rewrite ?Nat.add_0_r.
  rewrite <- map_eq_flatMap. apply map_ext; intro i. rewrite Nat.add_0_r. reflexivity.
Qed.
Theorem tapeCNF_bits : forall base x,
  tapeCNF base (map (fun b => fixed (ofBool b)) x) =
    map (fun i => [mkLit (base+4*i+(1+if nth i x false then 1 else 0)) true]) (seq 0 (length x)).
Proof.
  intros base x; revert base; induction x as [|b x IH]; intro base; [reflexivity|].
  cbn [length]. replace (S (length x)) with (length x+1) by lia. rewrite map_range_succ.
  cbn [map tapeCNF nth]. rewrite IH. rewrite Nat.mul_0_r, Nat.add_0_r.
  destruct b; cbn [sourceCNF ofBool symbolIndex app]; f_equal;
    apply map_ext; intro i; replace (i+1) with (S i) by lia; cbn [nth]; repeat (f_equal; try lia).
Qed.
Theorem certificateSources_range : forall start bound,
  certificateSources start bound = map (fun i => certificate (start+i)) (seq 0 bound).
Proof.
  intros start bound; revert start; induction bound as [|n IH]; intro start.
  - reflexivity.
  - replace (S n) with (n+1) by lia. rewrite map_range_succ.
    replace (n+1) with (S n) by lia. cbn [certificateSources]. rewrite IH, Nat.add_0_r.
    f_equal. apply map_ext; intro i. f_equal; lia.
Qed.
Theorem tapeCNF_certificate : forall base start bound,
  tapeCNF base (certificateSources start bound) =
    flat_map (fun i => sourceCNF (base+4*i) (certificate (start+i))) (seq 0 bound).
Proof. intros; rewrite certificateSources_range, tapeCNF_map_range; reflexivity. Qed.

Theorem initialSchema_eq : forall (m : Machine) (pairedInput : bool) (x : Word) B T W env,
  T + length x + (if pairedInput then 1+B else 0) <= W ->
  evalSchema (initialSchema m pairedInput) [length x;B;T;W] x env =
    initialCNF (2*B+1) (length (program m)) T
      (windowSources (if pairedInput then paired m else ignoreCertificate m) x B T W).
Proof.
  intros m pairedInput x B T W env hroom.
  assert (hw : length (windowSources (if pairedInput then paired m else ignoreCertificate m) x B T W) = W).
  { apply windowSources_length. destruct pairedInput; unfold inputSources;
      rewrite ?length_app, ?length_map, ?certificateSources_length; cbn [length] in *; lia. }
  unfold initialCNF. rewrite hw. unfold initialSchema. cbn [evalSchema].
  rewrite rowSchema_eq by (simpl; auto). cbn [evalExpr nth].
  destruct pairedInput; cbn [evalSchema evalLiterals evalExpr map fst snd nth];
    unfold windowSources, inputSources;
    rewrite !tapeCNF_append, ?length_app, ?length_map, ?repeat_length, ?certificateSources_length;
    cbn [length]; rewrite !tapeCNF_blank, !tapeCNF_bits, ?tapeCNF_certificate;
    cbn [tapeCNF sourceCNF symbolIndex app];
    rewrite ?sourceSchema_eq; cbn [evalExpr nth];
    rewrite <- !map_eq_flatMap; rewrite <- !app_assoc;
    rewrite ?Nat.sub_add_distr;
    repeat first [reflexivity | progress rewrite setIndex_same | solve [nia] | progress rewrite sourceSchema_eq |
      progress cbn [app setIndex evalExpr evalLiterals sourceCNF implies negate var pos map fst snd nth] |
      apply map_ext; intro i | apply flatMap_congr; intros i hi | progress f_equal].
Qed.
Theorem machineSchema_eq : forall (m : Machine) (pairedInput : bool) (x : Word) B T W env,
  T + length x + (if pairedInput then 1+B else 0) <= W ->
  evalSchema (machineSchema m pairedInput) [length x;B;T;W] x env =
    (certificateCNF 0 B ++ initialCNF (2*B+1) (length (program m)) T
      (windowSources (if pairedInput then paired m else ignoreCertificate m) x B T W)) ++
    runCNF m (2*B+1) W T.
Proof.
  intros m pairedInput x B T W env hroom. unfold machineSchema. cbn [evalSchema].
  rewrite certificateSchema_eq, initialSchema_eq, runSchema_eq by (simpl; auto).
  cbn [evalExpr nth]. rewrite app_assoc. reflexivity.
Qed.
Theorem tableauSchema_fragments : forall np x env,
  evalSchema (tableauSchema np) (tableauParams np (length x)) x env =
    (certificateCNF 0 (evalPoly (np_certBound np) (length x)) ++
      initialCNF (2*evalPoly (np_certBound np) (length x)+1)
        (length (program (verifierMachine (np_verifier np)))) (maxClock np (length x))
        (windowSources (np_verifier np) x (evalPoly (np_certBound np) (length x))
          (maxClock np (length x)) (windowWidth np (length x)))) ++
      runCNF (verifierMachine (np_verifier np)) (2*evalPoly (np_certBound np) (length x)+1)
        (windowWidth np (length x)) (maxClock np (length x)).
Proof.
  intros np x env. unfold tableauSchema, tableauParams.
  destruct (np_verifier np) as [m|m]; cbn [verifierMachine];
    rewrite machineSchema_eq by (unfold windowWidth; lia); reflexivity.
Qed.

End Schema.
