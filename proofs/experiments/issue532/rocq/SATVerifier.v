(** * Issue #532: SAT is in NP on the shared machine model

    Rocq twin of [proofs/experiments/issue532/lean/SATVerifier.lean]; theorem
    names are aligned (Lean dotted names such as [Reaches.trans'] become
    [reaches_trans']).

    This file proves [satInNP : SATInNP], that is [InNP SAT], by building an
    explicit verifier table for the [paired] verifier format of [ClassNP] and
    proving it correct and polynomially bounded.  No step of the argument is
    assumed, and the file uses no axioms.

    ** The certificate

    A certificate is a bit vector [c0 c1 ...]; variable [i] gets [ci], and
    variables past the end of the certificate get [false] (this is
    [toAssign]).  For a satisfiable formula the certificate
    [prefixOf a (length x)] works, because every variable of [decode x] is
    [< length x] ([varsBelow_decode]).  So the certificate bound is [n + 1]
    and the verifier accepts [(x, c)] iff [evalCNF (toAssign c) (decode x)].

    ** The tape and the codes

    The word [x] is read in bit pairs exactly as [decodeAux] reads it: [11] is
    a tick, [0p] a literal with polarity [p], [10] a clause end, and an odd
    trailing bit is dropped.  During the run the formula region holds a list
    of [Code]s, two cells each:
    - [tick = 11], [lit p = 0p], [cend = 10] (live codes, as in the input);
    - [dead = 0S] (a deleted tick or an already evaluated literal);
    - [satEnd = 1S] (the end of a clause that is already satisfied).

    No code starts with the separator [S] and none contains a blank, so a pair
    that starts with [S] is the end of the formula region, and the blank left
    of the formula marks the left end of the tape.

    ** The machine

    1. Parity pass ([pEven], [pOdd], [pErase]): walk right over [x] in pairs;
       if [x] has odd length, overwrite the trailing bit by [S].
    2. Rounds.  [seek] walks right over the [S] cells to the leftmost unread
       certificate bit [b], overwrites it by [S] and [ret b] walks left to the
       blank at the left end.  The sweep [sw b k s] then rewrites the formula
       pairwise ([roundAux]): the first live tick of every literal becomes
       [dead] (flag [k] records that this literal already lost a tick); a live
       literal with no live tick left has variable index [0] relative to this
       round, so it is evaluated with value [b], becomes [dead], and if it is
       true it sets the clause flag [s]; a live clause end with [s] set
       becomes [satEnd].  After the round every live literal refers to the
       next certificate bit with index [0].
    3. When [seek] meets the blank past the certificate, [retF] returns to the
       left end and the final pass [fin] evaluates every remaining live
       literal with value [false] ([finalAux]): it rejects at a live clause
       end whose clause has no true literal and accepts at the end of the
       formula region.

    The abstract value [evalT a T k s] of a code list is the value of the
    formula it denotes under [a]; [evalT_pairsOf] identifies it with
    [evalCNF a (decodeAux w k cur)] on the input, [round_eval] shows that one
    round shifts the assignment by one bit, and [finalAux_eq] handles the
    final pass.  The machine lemmas ([sweep], [finalSweep], [phase0],
    [roundReaches], [finalRun], [loopRun]) show that the table performs
    exactly these rewrites, and [verifier_run] puts them together: the
    verifier halts on every pair [(x, c)] within [5 (|x| + |c| + 2)^2] steps
    with the answer [evalCNF (toAssign c) (decode x)].

    Differences from the Lean file: [toAssign_nil] holds by conversion
    ([reflexivity]), so no function extensionality is needed; the pair
    recursion over input words is packaged as the induction principle
    [list_pair_ind]; step counts are written with [S] where Lean writes
    [t + 1]. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** ** Codes on the tape *)

(** A two-cell code of the formula region. *)
Inductive Code := tick | lit (p : bool) | cend | dead | satEnd.

(** The cells of one code. *)
Definition codeCells (x : Code) : list Symbol :=
  match x with
  | tick => [one; one]
  | lit p => [zero; ofBool p]
  | cend => [one; zero]
  | dead => [zero; separator]
  | satEnd => [one; separator]
  end.

(** The cells of a code list. *)
Fixpoint tapeOf (T : list Code) : list Symbol :=
  match T with
  | [] => []
  | x :: T' => codeCells x ++ tapeOf T'
  end.

(** The code of an input bit pair, as [decodeAux] reads it. *)
Definition pairCode (a b : bool) : Code :=
  match a, b with
  | true, true => tick
  | true, false => cend
  | false, p => lit p
  end.

(** The input read in bit pairs; an odd trailing bit is dropped. *)
Fixpoint pairsOf (w : list bool) : list Code :=
  match w with
  | a :: b :: r => pairCode a b :: pairsOf r
  | _ => []
  end.

(** Recursion over a word two bits at a time, as [decodeAux] and [pairsOf]. *)
Lemma list_pair_ind : forall (P : list bool -> Prop),
  P [] -> (forall a, P [a]) -> (forall a b r, P r -> P (a :: b :: r)) ->
  forall w, P w.
Proof.
  intros P h0 h1 h2. fix IH 1. intros w.
  destruct w as [| a [| b r]].
  - exact h0.
  - exact (h1 a).
  - exact (h2 a b r (IH r)).
Qed.

(** ** The abstract algorithm *)

(** The value under [a] of the formula denoted by a code list.  [k] counts the
    live ticks of the current literal and [s] is the value of the current
    clause so far.  An unfinished clause at the end is dropped, as in
    [decodeAux]. *)
Fixpoint evalT (a : Assignment) (T : list Code) (k : nat) (s : bool) : bool :=
  match T with
  | [] => true
  | tick :: r => evalT a r (S k) s
  | lit p :: r => evalT a r 0 (s || Bool.eqb (a k) p)
  | cend :: r => s && evalT a r 0 false
  | dead :: r => evalT a r k s
  | satEnd :: r => evalT a r 0 false
  end.

(** One code of a sweep with certificate bit [b]: returns the rewritten code
    and the new flags ([k]: this literal already lost a tick; [s]: the current
    clause is already satisfied by a literal evaluated in this round). *)
Definition roundStep (b k s : bool) (x : Code) : Code * (bool * bool) :=
  match x with
  | tick => if k then (tick, (true, s)) else (dead, (true, s))
  | lit p => if k then (lit p, (false, s)) else (dead, (false, s || Bool.eqb p b))
  | cend => (if s then satEnd else cend, (false, false))
  | dead => (dead, (k, s))
  | satEnd => (satEnd, (false, false))
  end.

(** A sweep with certificate bit [b]. *)
Fixpoint roundAux (b : bool) (k s : bool) (T : list Code) : list Code :=
  match T with
  | [] => []
  | x :: T' =>
    fst (roundStep b k s x) ::
      roundAux b (fst (snd (roundStep b k s x))) (snd (snd (roundStep b k s x))) T'
  end.

(** All rounds, one per certificate bit, from the first bit on. *)
Fixpoint rounds (c : list bool) (T : list Code) : list Code :=
  match c with
  | [] => T
  | b :: c' => rounds c' (roundAux b false false T)
  end.

(** The final pass: every remaining live literal is evaluated with value
    [false], so only negative live literals are true. *)
Fixpoint finalAux (s : bool) (T : list Code) : bool :=
  match T with
  | [] => true
  | tick :: r => finalAux s r
  | lit p :: r => finalAux (s || negb p) r
  | cend :: r => s && finalAux false r
  | dead :: r => finalAux s r
  | satEnd :: r => finalAux false r
  end.

(** ** Correctness of the abstract algorithm *)

Theorem evalClause_append : forall (a : Assignment) (cur : Clause) (l : Lit),
  evalClause a (cur ++ [l]) = (evalClause a cur || evalLit a l).
Proof.
  intros a cur l. induction cur as [| l' c IH]; simpl.
  - destruct (evalLit a l); reflexivity.
  - rewrite IH. apply orb_assoc.
Qed.

(** On the input, [evalT] is the value of the decoded formula. *)
Theorem evalT_pairsOf : forall (a : Assignment) (w : list bool) (k : nat) (cur : Clause),
  evalT a (pairsOf w) k (evalClause a cur) = evalCNF a (decodeAux w k cur).
Proof.
  intros a w. induction w as [| x | x p r IH] using list_pair_ind; intros k cur.
  - reflexivity.
  - destruct x; reflexivity.
  - destruct x; [destruct p |]; simpl.
    + apply IH.
    + f_equal. exact (IH 0 []).
    + rewrite <- IH, evalClause_append. reflexivity.
Qed.

(** One round with bit [b = a 0] turns the value under [a] into the value
    under the shifted assignment [a']. *)
Theorem round_eval : forall (a a' : Assignment) (b : bool), a 0 = b ->
  (forall i, a (S i) = a' i) ->
  forall (T : list Code) (s' sn : bool),
    (forall k', evalT a' (roundAux b true s' T) k' sn = evalT a T (S k') (sn || s')) /\
    evalT a' (roundAux b false s' T) 0 sn = evalT a T 0 (sn || s').
Proof.
  intros a a' b ha0 has T. induction T as [| x T IH]; intros s' sn.
  - split; [intros k' |]; reflexivity.
  - destruct x as [| p | | |]; split; [intros k' | | intros k' | | intros k' | |
      intros k' | | intros k' |]; simpl.
    + exact (proj1 (IH s' sn) (S k')).
    + exact (proj1 (IH s' sn) 0).
    + rewrite (proj2 (IH s' _)), has.
      destruct sn, s', (Bool.eqb (a' k') p); reflexivity.
    + rewrite (proj2 (IH _ sn)), ha0.
      destruct sn, s', p, b; reflexivity.
    + destruct s'; simpl; rewrite (proj2 (IH false false)); destruct sn; reflexivity.
    + destruct s'; simpl; rewrite (proj2 (IH false false)); destruct sn; reflexivity.
    + exact (proj1 (IH s' sn) k').
    + exact (proj2 (IH s' sn)).
    + rewrite (proj2 (IH false false)). reflexivity.
    + rewrite (proj2 (IH false false)). reflexivity.
Qed.

(** The final pass is the value under the all-[false] assignment. *)
Theorem finalAux_eq : forall (T : list Code) (k : nat) (s : bool),
  finalAux s T = evalT (fun _ => false) T k s.
Proof.
  intros T. induction T as [| x T IH]; intros k s.
  - reflexivity.
  - destruct x as [| p | | |]; simpl.
    + apply IH.
    + rewrite (IH 0). destruct p; reflexivity.
    + rewrite (IH 0). reflexivity.
    + apply IH.
    + apply IH.
Qed.

(** [toAssign []] is the all-[false] assignment, by conversion. *)
Theorem toAssign_nil : toAssign [] = (fun _ => false).
Proof. reflexivity. Qed.

(** The rounds followed by the final pass compute the value under the
    certificate assignment. *)
Theorem rounds_eval : forall (c : list bool) (T : list Code),
  finalAux false (rounds c T) = evalT (toAssign c) T 0 false.
Proof.
  intros c. induction c as [| b c IH]; intros T.
  - rewrite toAssign_nil. apply finalAux_eq.
  - simpl. rewrite IH.
    exact (proj2 (round_eval (toAssign (b :: c)) (toAssign c) b eq_refl
      (fun _ => eq_refl) T false false)).
Qed.

(** The abstract verifier computes [evalCNF (toAssign c) (decode x)]. *)
Theorem accept_value : forall x c : list bool,
  finalAux false (rounds c (pairsOf x)) = evalCNF (toAssign c) (decode x).
Proof.
  intros x c. rewrite rounds_eval. exact (evalT_pairsOf (toAssign c) x 0 []).
Qed.

(** ** Every variable of the decoded formula is below the input length *)

Theorem varsBelow_decodeAux : forall (n : nat) (w : list bool) (k : nat) (cur : Clause),
  k + length w <= n -> (forall l, In l cur -> var l < n) ->
  VarsBelow n (decodeAux w k cur).
Proof.
  intros n w. induction w as [| x | x p r IH] using list_pair_ind;
    intros k cur hk hcur.
  - intros c hc. destruct hc.
  - intros c hc. destruct x; destruct hc.
  - simpl in hk. destruct x; [destruct p |]; simpl.
    + apply IH; [lia | exact hcur].
    + intros c [hc | hc].
      * subst c. exact hcur.
      * apply (IH 0 []); [lia | intros l [] | exact hc].
    + apply IH; [lia |].
      intros l hl. apply in_app_iff in hl. destruct hl as [hl | [hl | []]].
      * exact (hcur l hl).
      * subst l. simpl. lia.
Qed.

Theorem varsBelow_decode : forall x : list bool, VarsBelow (length x) (decode x).
Proof.
  intros x. apply varsBelow_decodeAux; [lia | intros l []].
Qed.

(** ** The machine *)

(** Named machine states. *)
Inductive St :=
  | pEven | pOdd | pErase
  | seek
  | ret (b : bool)
  | retF
  | fin (s : bool) | fin0 (s : bool) | fin1 (s : bool)
  | sw (b k s : bool) | sw0 (b k s : bool) | sw1 (b k s : bool)
  | back (b s : bool) | fwd (b s : bool).

(** Three flags as a number below [8]. *)
Definition bits3 (b k s : bool) : nat := 4 * Nat.b2n b + 2 * Nat.b2n k + Nat.b2n s.

(** State numbers; [pEven] is the initial state [0]. *)
Definition idx (q : St) : nat :=
  match q with
  | pEven => 0
  | pOdd => 1
  | pErase => 2
  | seek => 3
  | ret b => 4 + Nat.b2n b
  | retF => 6
  | fin s => 7 + Nat.b2n s
  | fin0 s => 9 + Nat.b2n s
  | fin1 s => 11 + Nat.b2n s
  | sw b k s => 13 + bits3 b k s
  | sw0 b k s => 21 + bits3 b k s
  | sw1 b k s => 29 + bits3 b k s
  | back b s => 37 + 2 * Nat.b2n b + Nat.b2n s
  | fwd b s => 41 + 2 * Nat.b2n b + Nat.b2n s
  end.

Definition triples : list (bool * (bool * bool)) :=
  [(false, (false, false)); (false, (false, true)); (false, (true, false));
   (false, (true, true)); (true, (false, false)); (true, (false, true));
   (true, (true, false)); (true, (true, true))].

Definition pairs2 : list (bool * bool) :=
  [(false, false); (false, true); (true, false); (true, true)].

(** All states, listed in the order of [idx]. *)
Definition allStates : list St :=
  [pEven; pOdd; pErase; seek; ret false; ret true; retF; fin false; fin true;
   fin0 false; fin0 true; fin1 false; fin1 true] ++
  map (fun t => sw (fst t) (fst (snd t)) (snd (snd t))) triples ++
  map (fun t => sw0 (fst t) (fst (snd t)) (snd (snd t))) triples ++
  map (fun t => sw1 (fst t) (fst (snd t)) (snd (snd t))) triples ++
  map (fun t => back (fst t) (snd t)) pairs2 ++
  map (fun t => fwd (fst t) (snd t)) pairs2.

Theorem allStates_idx : forall q : St, nth_error allStates (idx q) = Some q.
Proof.
  intros q.
  destruct q as [| | | | b | | s | s | s | b k s | b k s | b k s | b s | b s];
    try destruct b; try destruct k; try destruct s; reflexivity.
Qed.

Definition mv (q : St) (w : Symbol) (d : Direction) : Instruction := move (idx q) w d.

(** The transition table, by state and scanned symbol. *)
Definition deltaSt (q : St) (a : Symbol) : Instruction :=
  match q, a with
  (* parity pass *)
  | pEven, zero => mv pOdd zero right
  | pEven, one => mv pOdd one right
  | pEven, separator => mv seek separator stay
  | pOdd, zero => mv pEven zero right
  | pOdd, one => mv pEven one right
  | pOdd, separator => mv pErase separator left
  | pErase, zero => mv seek separator stay
  | pErase, one => mv seek separator stay
  (* find and erase the next certificate bit *)
  | seek, separator => mv seek separator right
  | seek, zero => mv (ret false) separator left
  | seek, one => mv (ret true) separator left
  | seek, blank => mv retF blank left
  (* return to the left end *)
  | ret b, blank => mv (sw b false false) blank right
  | ret b, zero => mv (ret b) zero left
  | ret b, one => mv (ret b) one left
  | ret b, separator => mv (ret b) separator left
  | retF, blank => mv (fin false) blank right
  | retF, zero => mv retF zero left
  | retF, one => mv retF one left
  | retF, separator => mv retF separator left
  (* final pass *)
  | fin _, separator => halt true
  | fin s, zero => mv (fin0 s) zero right
  | fin s, one => mv (fin1 s) one right
  | fin0 _, zero => mv (fin true) zero right
  | fin0 s, one => mv (fin s) one right
  | fin0 s, separator => mv (fin s) separator right
  | fin1 s, one => mv (fin s) one right
  | fin1 s, zero => if s then mv (fin false) zero right else halt false
  | fin1 _, separator => mv (fin false) separator right
  (* one sweep with certificate bit [b] *)
  | sw _ _ _, separator => mv seek separator stay
  | sw b k s, zero => mv (sw0 b k s) zero right
  | sw b k s, one => mv (sw1 b k s) one right
  | sw0 b k s, separator => mv (sw b k s) separator right
  | sw0 b k s, zero =>
    if k then mv (sw b false s) zero right
    else mv (sw b false (s || Bool.eqb false b)) separator right
  | sw0 b k s, one =>
    if k then mv (sw b false s) one right
    else mv (sw b false (s || Bool.eqb true b)) separator right
  | sw1 b k s, one =>
    if k then mv (sw b true s) one right else mv (back b s) separator left
  | sw1 b _ s, zero =>
    if s then mv (sw b false false) separator right
    else mv (sw b false false) zero right
  | sw1 b _ _, separator => mv (sw b false false) separator right
  | back b s, one => mv (fwd b s) zero right
  | fwd b s, separator => mv (sw b true s) separator right
  | _, _ => halt false
  end.

(** The row of a state, indexed by [symbolIndex]. *)
Definition row (q : St) : list Instruction :=
  [deltaSt q blank; deltaSt q zero; deltaSt q one; deltaSt q separator].

(** The verifier table. *)
Definition verifier : Machine := {| program := map row allStates |}.

Theorem instr : forall (q : St) (a : Symbol),
  instruction verifier (idx q) a = deltaSt q a.
Proof.
  intros q a. unfold instruction, verifier. cbn [program].
  rewrite nth_error_map, allStates_idx. destruct a; reflexivity.
Qed.

(** ** Configurations and single steps *)

(** State [q], reversed left part [L], and the cells from the head on; an
    empty cell list means a blank head at the right end. *)
Definition cfg (q : St) (L : list Symbol) (R : list Symbol) : Config :=
  match R with
  | [] => {| state := idx q; tapeLeft := L; tapeHead := blank; tapeRight := [] |}
  | a :: R' => {| state := idx q; tapeLeft := L; tapeHead := a; tapeRight := R' |}
  end.

Theorem cfg_nil : forall q L, cfg q L [] = cfg q L [blank].
Proof. reflexivity. Qed.

Theorem stepR : forall q q' a w, deltaSt q a = mv q' w right ->
  forall L R, step verifier (cfg q L (a :: R)) = inr (cfg q' (w :: L) R).
Proof.
  intros q q' a w h L R. unfold step. cbn [cfg state tapeHead].
  rewrite instr, h. unfold mv. destruct R; reflexivity.
Qed.

Theorem stepL : forall q q' a w, deltaSt q a = mv q' w left ->
  forall l L R, step verifier (cfg q (l :: L) (a :: R)) = inr (cfg q' L (l :: w :: R)).
Proof.
  intros q q' a w h l L R. unfold step. cbn [cfg state tapeHead].
  rewrite instr, h. reflexivity.
Qed.

Theorem stepL0 : forall q q' a w, deltaSt q a = mv q' w left ->
  forall R, step verifier (cfg q [] (a :: R)) = inr (cfg q' [] (blank :: w :: R)).
Proof.
  intros q q' a w h R. unfold step. cbn [cfg state tapeHead].
  rewrite instr, h. reflexivity.
Qed.

Theorem stepS : forall q q' a w, deltaSt q a = mv q' w stay ->
  forall L R, step verifier (cfg q L (a :: R)) = inr (cfg q' L (w :: R)).
Proof.
  intros q q' a w h L R. unfold step. cbn [cfg state tapeHead].
  rewrite instr, h. reflexivity.
Qed.

Theorem stepH : forall q a b, deltaSt q a = halt b ->
  forall L R, step verifier (cfg q L (a :: R)) = inl b.
Proof.
  intros q a b h L R. unfold step. cbn [cfg state tapeHead].
  rewrite instr, h. reflexivity.
Qed.

(** ** Partial runs *)

(** From here on [simpl] keeps configurations in the [cfg] form. *)
Arguments cfg : simpl never.

Theorem reaches_trans' : forall m c d e t u,
  Reaches m c t d -> Reaches m d u e -> Reaches m c (t + u) e.
Proof.
  intros m c d e t u h h'. induction h as [c | c c' d t hs _ IH].
  - exact h'.
  - simpl. exact (reaches_next m c c' e (t + u) hs (IH h')).
Qed.

Theorem R1 : forall q q' a w L R t E, deltaSt q a = mv q' w right ->
  Reaches verifier (cfg q' (w :: L) R) t E -> Reaches verifier (cfg q L (a :: R)) (S t) E.
Proof.
  intros q q' a w L R t E h hr. exact (reaches_next _ _ _ _ _ (stepR q q' a w h L R) hr).
Qed.

Theorem L1 : forall q q' a w l L R t E, deltaSt q a = mv q' w left ->
  Reaches verifier (cfg q' L (l :: w :: R)) t E -> Reaches verifier (cfg q (l :: L) (a :: R)) (S t) E.
Proof.
  intros q q' a w l L R t E h hr.
  exact (reaches_next _ _ _ _ _ (stepL q q' a w h l L R) hr).
Qed.

Theorem S1 : forall q q' a w L R t E, deltaSt q a = mv q' w stay ->
  Reaches verifier (cfg q' L (w :: R)) t E -> Reaches verifier (cfg q L (a :: R)) (S t) E.
Proof.
  intros q q' a w L R t E h hr. exact (reaches_next _ _ _ _ _ (stepS q q' a w h L R) hr).
Qed.

(** Run a fixed number of explicit table steps. *)
Ltac go := solve [repeat first
  [ eapply R1; [reflexivity |]
  | eapply L1; [reflexivity |]
  | eapply S1; [reflexivity |]
  | apply reaches_refl ]].

(** ** Sweeps *)

(** One code of a sweep takes at most four steps (four for a deleted tick,
    which needs one step back to rewrite the first cell). *)
Theorem sweepCode : forall (b k s : bool) (x : Code) (L R : list Symbol),
  exists t, t <= 4 /\
    Reaches verifier (cfg (sw b k s) L (codeCells x ++ R)) t
      (cfg (sw b (fst (snd (roundStep b k s x))) (snd (snd (roundStep b k s x))))
        (rev (codeCells (fst (roundStep b k s x))) ++ L) R).
Proof.
  intros b k s x L R.
  destruct x as [| p | | |]; [destruct k | destruct k, p | destruct s | |]; simpl;
    first [ exists 4; split; [lia | go] | exists 2; split; [lia | go] ].
Qed.

Theorem tapeOf_cons : forall x T, tapeOf (x :: T) = codeCells x ++ tapeOf T.
Proof. reflexivity. Qed.

(** A whole sweep: the formula region is rewritten by [roundAux] and the
    machine stops in [seek] on the separator that ends the region. *)
Theorem sweep : forall (b : bool) (T : list Code) (k s : bool) (L R : list Symbol),
  exists t, t <= 4 * length T + 1 /\
    Reaches verifier (cfg (sw b k s) L (tapeOf T ++ separator :: R)) t
      (cfg seek (rev (tapeOf (roundAux b k s T)) ++ L) (separator :: R)).
Proof.
  intros b T. induction T as [| x T IH]; intros k s L R.
  - exists 1. split; [simpl; lia | simpl; go].
  - destruct (sweepCode b k s x L (tapeOf T ++ separator :: R)) as [t1 [ht1 h1]].
    destruct (IH (fst (snd (roundStep b k s x))) (snd (snd (roundStep b k s x)))
      (rev (codeCells (fst (roundStep b k s x))) ++ L) R) as [t2 [ht2 h2]].
    exists (t1 + t2). split; [simpl; lia |].
    rewrite tapeOf_cons, <- app_assoc.
    cbn [roundAux]. rewrite tapeOf_cons, rev_app_distr, <- app_assoc.
    exact (reaches_trans' _ _ _ _ _ _ h1 h2).
Qed.

(** The final pass accepts or rejects as [finalAux]. *)
Theorem finalSweep : forall (T : list Code) (s : bool) (L R : list Symbol),
  exists t, t <= 2 * length T + 1 /\
    Run verifier (cfg (fin s) L (tapeOf T ++ separator :: R)) t (finalAux s T).
Proof.
  intros T. induction T as [| x T IH]; intros s L R.
  - exists 1. split; [simpl; lia |].
    apply run_halt. apply stepH. reflexivity.
  - destruct x as [| p | | |].
    + destruct (IH s (one :: one :: L) R) as [t [ht h]].
      exists (2 + t). split; [simpl; lia |].
      eapply reaches_run; [| exact h]. simpl. go.
    + destruct p.
      * destruct (IH s (one :: zero :: L) R) as [t [ht h]].
        exists (2 + t). split; [simpl; lia |].
        simpl finalAux. rewrite orb_false_r.
        eapply reaches_run; [| exact h]. simpl. go.
      * destruct (IH true (zero :: zero :: L) R) as [t [ht h]].
        exists (2 + t). split; [simpl; lia |].
        simpl finalAux. rewrite orb_true_r.
        eapply reaches_run; [| exact h]. simpl. go.
    + destruct s.
      * destruct (IH false (zero :: one :: L) R) as [t [ht h]].
        exists (2 + t). split; [simpl; lia |].
        eapply reaches_run; [| exact h]. simpl. go.
      * exists 2. split; [simpl; lia |].
        simpl. eapply run_next; [apply stepR; reflexivity |].
        apply run_halt. apply stepH. reflexivity.
    + destruct (IH s (separator :: zero :: L) R) as [t [ht h]].
      exists (2 + t). split; [simpl; lia |].
      eapply reaches_run; [| exact h]. simpl. go.
    + destruct (IH false (separator :: one :: L) R) as [t [ht h]].
      exists (2 + t). split; [simpl; lia |].
      eapply reaches_run; [| exact h]. simpl. go.
Qed.

(** ** Walking over the tape *)

Theorem walkR : forall (q : St) (w L R : list Symbol),
  (forall a, In a w -> deltaSt q a = mv q a right) ->
  Reaches verifier (cfg q L (w ++ R)) (length w) (cfg q (rev w ++ L) R).
Proof.
  intros q w. induction w as [| a w IH]; intros L R h.
  - apply reaches_refl.
  - simpl. rewrite <- app_assoc. simpl.
    apply (R1 q q a a L (w ++ R)); [apply h; left; reflexivity |].
    apply IH. intros a' ha'. apply h. right. exact ha'.
Qed.

(** Walking left to the blank at the left end.  The part left of the formula
    is either empty (first time) or the single blank cell created by the first
    walk. *)
Theorem walkLEnd : forall (q : St) (Lb : list Symbol), Lb = [] \/ Lb = [blank] ->
  forall (w : list Symbol) (a : Symbol) (R : list Symbol),
    (forall a', In a' (a :: w) -> deltaSt q a' = mv q a' left) ->
    Reaches verifier (cfg q (w ++ Lb) (a :: R)) (S (length w))
      (cfg q [] (blank :: rev w ++ a :: R)).
Proof.
  intros q Lb hLb w. induction w as [| l w IH]; intros a R h.
  - assert (ha : deltaSt q a = mv q a left) by (apply h; left; reflexivity).
    destruct hLb as [e | e]; subst Lb; simpl.
    + exact (reaches_next _ _ _ _ _ (stepL0 q q a a ha R) (reaches_refl _ _)).
    + exact (reaches_next _ _ _ _ _ (stepL q q a a ha blank [] R) (reaches_refl _ _)).
  - simpl. apply (L1 q q a a l (w ++ Lb) R); [apply h; left; reflexivity |].
    rewrite <- app_assoc. simpl.
    apply IH. intros a' [e | ha']; apply h; [subst; right; left; reflexivity |].
    right; right; exact ha'.
Qed.

Theorem ret_left : forall (b : bool) (a : Symbol), a <> blank ->
  deltaSt (ret b) a = mv (ret b) a left.
Proof. intros b a ha. destruct a; [contradiction | reflexivity..]. Qed.

Theorem retF_left : forall a : Symbol, a <> blank -> deltaSt retF a = mv retF a left.
Proof. intros a ha. destruct a; [contradiction | reflexivity..]. Qed.

Theorem codeCells_ne_blank : forall (x : Code) a, In a (codeCells x) -> a <> blank.
Proof.
  intros x a ha. destruct x as [| p | | |]; [| destruct p | | |]; simpl in ha;
    repeat destruct ha as [ha | ha]; subst; try discriminate; contradiction.
Qed.

Theorem tapeOf_ne_blank : forall (T : list Code) a, In a (tapeOf T) -> a <> blank.
Proof.
  intros T. induction T as [| x T IH]; intros a h.
  - destruct h.
  - rewrite tapeOf_cons in h. apply in_app_iff in h. destruct h as [h | h].
    + exact (codeCells_ne_blank x a h).
    + exact (IH a h).
Qed.

Theorem length_codeCells : forall x : Code, length (codeCells x) = 2.
Proof. intros x. destruct x; reflexivity. Qed.

Theorem length_tapeOf : forall T : list Code, length (tapeOf T) = 2 * length T.
Proof.
  intros T. induction T as [| x T IH]; [reflexivity |].
  rewrite tapeOf_cons, length_app, length_codeCells, IH. simpl. lia.
Qed.

Theorem length_roundAux : forall (b k s : bool) (T : list Code),
  length (roundAux b k s T) = length T.
Proof.
  intros b k s T. revert k s. induction T as [| x T IH]; intros k s; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Theorem length_pairsOf : forall x : list bool, 2 * length (pairsOf x) <= length x.
Proof.
  intros x. induction x as [| a | a b r IH] using list_pair_ind; simpl in *; lia.
Qed.

Theorem codeCells_pairCode : forall a b : bool,
  codeCells (pairCode a b) = [ofBool a; ofBool b].
Proof. intros a b. destruct a, b; reflexivity. Qed.

Theorem replicate_cons_eq : forall (n : nat) (a : Symbol) (l : list Symbol),
  repeat a n ++ a :: l = a :: (repeat a n ++ l).
Proof.
  intros n a l. induction n as [| n IH]; [reflexivity |].
  simpl. rewrite IH. reflexivity.
Qed.

(** ** The parity pass *)

Theorem phase0 : forall (x : list bool) (L R : list Symbol), exists t m,
  t <= length x + 2 /\ 1 <= m /\ m <= 2 /\
    Reaches verifier (cfg pEven L (map ofBool x ++ separator :: R)) t
      (cfg seek (rev (tapeOf (pairsOf x)) ++ L) (repeat separator m ++ R)).
Proof.
  intros x. induction x as [| a | a b r IH] using list_pair_ind; intros L R.
  - exists 1, 1. split; [simpl; lia |]. split; [lia |]. split; [lia |].
    simpl. go.
  - exists 3, 2. split; [simpl; lia |]. split; [lia |]. split; [lia |].
    destruct a; simpl; go.
  - destruct (IH (ofBool b :: ofBool a :: L) R) as [t [m [ht [hm1 [hm2 h]]]]].
    exists (S (S t)), m. split; [simpl; lia |]. split; [exact hm1 |]. split; [exact hm2 |].
    assert (e : rev (tapeOf (pairsOf (a :: b :: r))) ++ L =
        rev (tapeOf (pairsOf r)) ++ ofBool b :: ofBool a :: L).
    { simpl. rewrite codeCells_pairCode, rev_app_distr, <- app_assoc. reflexivity. }
    rewrite e. simpl.
    destruct a, b; (eapply R1; [reflexivity |]; eapply R1; [reflexivity |]; exact h).
Qed.

(** ** Rounds and the final pass on the tape *)

Definition seps (n : nat) : list Symbol := repeat separator n.

Theorem seps_right : forall n a, In a (seps n) -> deltaSt seek a = mv seek a right.
Proof. intros n a ha. unfold seps in ha. rewrite (repeat_spec n separator a ha). reflexivity. Qed.

Theorem seps_ne_blank : forall n a, In a (seps n) -> a <> blank.
Proof. intros n a ha. unfold seps in ha. rewrite (repeat_spec n separator a ha). discriminate. Qed.

Theorem left_part_ne_blank : forall (n : nat) (T : list Code) a,
  In a (separator :: (seps n ++ rev (tapeOf T))) -> a <> blank.
Proof.
  intros n T a [h | h]; [subst; discriminate |].
  apply in_app_iff in h. destruct h as [h | h].
  - exact (seps_ne_blank n a h).
  - apply in_rev in h. exact (tapeOf_ne_blank T a h).
Qed.

(** One round: erase the next certificate bit [b], return to the left end and
    sweep the formula region with [b]. *)
Theorem roundReaches : forall (b : bool) (c : list bool) (T : list Code) (m : nat)
    (Lb : list Symbol), Lb = [] \/ Lb = [blank] -> 1 <= m ->
  exists t, t <= 2 * m + 6 * length T + 3 /\
    Reaches verifier (cfg seek (rev (tapeOf T) ++ Lb) (seps m ++ ofBool b :: map ofBool c))
      t (cfg seek (rev (tapeOf (roundAux b false false T)) ++ [blank])
        (seps (S m) ++ map ofBool c)).
Proof.
  intros b c T m Lb hLb hm.
  destruct m as [| m']; [lia |].
  assert (h1 : Reaches verifier
      (cfg seek (rev (tapeOf T) ++ Lb) (seps (S m') ++ ofBool b :: map ofBool c)) (S m')
      (cfg seek (separator :: seps m' ++ rev (tapeOf T) ++ Lb) (ofBool b :: map ofBool c))).
  { pose proof (walkR seek (seps (S m')) (rev (tapeOf T) ++ Lb)
      (ofBool b :: map ofBool c) (seps_right (S m'))) as h.
    unfold seps in *. rewrite rev_repeat, repeat_length in h. exact h. }
  assert (hb : deltaSt seek (ofBool b) = mv (ret b) separator left) by (destruct b; reflexivity).
  pose proof (walkLEnd (ret b) Lb hLb (seps m' ++ rev (tapeOf T)) separator
    (separator :: map ofBool c)
    (fun a ha => ret_left b a (left_part_ne_blank m' T a ha))) as h3.
  rewrite <- app_assoc in h3.
  pose proof (L1 _ _ _ _ _ _ _ _ _ hb h3) as h2.
  pose proof (reaches_trans' _ _ _ _ _ _ h1 h2) as h4.
  destruct (sweep b T false false [blank] (seps (S m') ++ map ofBool c)) as [t5 [ht5 h5]].
  pose proof (R1 (ret b) (sw b false false) blank blank [] _ _ _ eq_refl h5) as h45.
  assert (e : rev (seps m' ++ rev (tapeOf T)) ++ separator :: separator :: map ofBool c =
      tapeOf T ++ separator :: (seps (S m') ++ map ofBool c)).
  { rewrite rev_app_distr, rev_involutive. unfold seps. rewrite rev_repeat, <- app_assoc.
    f_equal. rewrite replicate_cons_eq, replicate_cons_eq. reflexivity. }
  rewrite <- e in h45.
  pose proof (reaches_trans' _ _ _ _ _ _ h4 h45) as h.
  eexists. split; [| exact h].
  rewrite length_app, length_rev, length_tapeOf. unfold seps. rewrite repeat_length. lia.
Qed.

(** The certificate is used up: return to the left end and run the final
    pass. *)
Theorem finalRun : forall (T : list Code) (m : nat) (Lb : list Symbol),
  Lb = [] \/ Lb = [blank] -> 1 <= m ->
  exists t, t <= 2 * m + 4 * length T + 3 /\
    Run verifier (cfg seek (rev (tapeOf T) ++ Lb) (seps m)) t (finalAux false T).
Proof.
  intros T m Lb hLb hm.
  destruct m as [| m']; [lia |].
  assert (h1 : Reaches verifier (cfg seek (rev (tapeOf T) ++ Lb) (seps (S m'))) (S m')
      (cfg seek (separator :: seps m' ++ rev (tapeOf T) ++ Lb) [blank])).
  { pose proof (walkR seek (seps (S m')) (rev (tapeOf T) ++ Lb) [] (seps_right (S m'))) as h.
    unfold seps in *. rewrite rev_repeat, repeat_length, cfg_nil, app_nil_r in h. exact h. }
  pose proof (walkLEnd retF Lb hLb (seps m' ++ rev (tapeOf T)) separator [blank]
    (fun a ha => retF_left a (left_part_ne_blank m' T a ha))) as h3.
  rewrite <- app_assoc in h3.
  pose proof (L1 seek retF blank blank _ _ _ _ _ eq_refl h3) as h2.
  pose proof (reaches_trans' _ _ _ _ _ _ h1 h2) as h4.
  destruct (finalSweep T false [blank] (seps m' ++ [blank])) as [t5 [ht5 h5]].
  pose proof (reaches_run _ _ _ _ _ _
    (R1 retF (fin false) blank blank [] _ _ _ eq_refl (reaches_refl _ _)) h5) as h45.
  assert (e : rev (seps m' ++ rev (tapeOf T)) ++ [separator; blank] =
      tapeOf T ++ separator :: (seps m' ++ [blank])).
  { rewrite rev_app_distr, rev_involutive. unfold seps. rewrite rev_repeat, <- app_assoc.
    f_equal. apply replicate_cons_eq. }
  rewrite <- e in h45.
  pose proof (reaches_run _ _ _ _ _ _ h4 h45) as h.
  eexists. split; [| exact h].
  rewrite length_app, length_rev, length_tapeOf. unfold seps. rewrite repeat_length. lia.
Qed.

(** All rounds and the final pass. *)
Theorem loopRun : forall (c : list bool) (T : list Code) (m : nat) (Lb : list Symbol),
  Lb = [] \/ Lb = [blank] -> 1 <= m ->
  exists t, t <= (length c + 1) * (2 * (m + length c) + 6 * length T + 4) /\
    Run verifier (cfg seek (rev (tapeOf T) ++ Lb) (seps m ++ map ofBool c)) t
      (finalAux false (rounds c T)).
Proof.
  intros c. induction c as [| b c IH]; intros T m Lb hLb hm.
  - destruct (finalRun T m Lb hLb hm) as [t [ht h]].
    exists t. split; [simpl; lia |]. simpl. rewrite app_nil_r. exact h.
  - destruct (roundReaches b c T m Lb hLb hm) as [t1 [ht1 h1]].
    destruct (IH (roundAux b false false T) (S m) [blank] (or_intror eq_refl)
      ltac:(lia)) as [t2 [ht2 h2]].
    exists (t1 + t2). split; [| exact (reaches_run _ _ _ _ _ _ h1 h2)].
    rewrite length_roundAux in ht2. simpl length. nia.
Qed.

(** ** The whole run on a paired input *)

Theorem initialSymbols_eq : forall l : list Symbol, initialSymbols l = cfg pEven [] l.
Proof. intros l. destruct l; reflexivity. Qed.

(** On input [x # c] the verifier halts within [5 (|x| + |c| + 2)^2] steps and
    answers whether [toAssign c] satisfies [decode x]. *)
Theorem verifier_run : forall x c : list bool, exists t,
  t <= 5 * (length x + length c + 1 + 1) ^ 2 /\
    Run verifier (pairedInput x c) t (evalCNF (toAssign c) (decode x)).
Proof.
  intros x c.
  assert (e : pairedInput x c =
      cfg pEven [] (map ofBool x ++ separator :: map ofBool c)).
  { unfold pairedInput. rewrite initialSymbols_eq. reflexivity. }
  destruct (phase0 x [] (map ofBool c)) as [t1 [m [ht1 [hm1 [hm2 h1]]]]].
  destruct (loopRun c (pairsOf x) m [] (or_introl eq_refl) hm1) as [t2 [ht2 h2]].
  rewrite accept_value in h2.
  exists (t1 + t2). split.
  - pose proof (length_pairsOf x) as hp.
    set (N := length x + length c + 1 + 1).
    assert (hA : (length c + 1) * (2 * (m + length c) + 6 * length (pairsOf x) + 4) <=
        N * (4 * N)) by (apply Nat.mul_le_mono; unfold N; lia).
    assert (hB : N <= N * N) by nia.
    rewrite Nat.pow_2_r. lia.
  - rewrite e. exact (reaches_run _ _ _ _ _ _ h1 h2).
Qed.

(** ** The NP record *)

(** The verifier for SAT: certificate bound [n + 1], time bound
    [5 (n + 1)^2]. *)
Definition satNP : ClassNP.
Proof.
  refine {| np_language := SAT;
            np_verifier := paired verifier;
            np_timeBound := {| coefficient := 5; degree := 2 |};
            np_certBound := {| coefficient := 1; degree := 1 |} |}.
  - intros x cert _.
    destruct (verifier_run x cert) as [t [ht h]].
    exists t, (evalCNF (toAssign cert) (decode x)). split; [exact ht | exact h].
  - intros x. split.
    + intros hx.
      destruct (proj1 (sat_iff x) hx) as [a ha].
      exists (prefixOf a (length x)).
      destruct (verifier_run x (prefixOf a (length x))) as [t [ht h]].
      assert (hv : evalCNF (toAssign (prefixOf a (length x))) (decode x) = true).
      { rewrite (evalCNF_congr (toAssign (prefixOf a (length x))) a (length x) (decode x)
          (fun i hi => toAssign_prefixOf a (length x) i hi) (varsBelow_decode x)).
        exact ha. }
      rewrite hv in h.
      exists t. split; [| split; [exact ht | exact h]].
      rewrite length_prefixOf. unfold evalPoly. simpl. lia.
    + intros [cert [t [_ [_ h]]]].
      destruct (verifier_run x cert) as [t' [_ h']].
      destruct (run_deterministic _ _ _ _ _ _ h h') as [_ hb].
      apply (proj2 (sat_iff x)). exists (toAssign cert). symmetry. exact hb.
Defined.

(** SAT is in NP, on the shared machine model. *)
Theorem satInNP : SATInNP.
Proof. exists satNP. reflexivity. Qed.

(** P = NP puts SAT in P (membership half of Cook-Levin now proved). *)
Theorem inP_sat_of_pEqualsNP' : PEqualsNP -> InP SAT.
Proof. intros h. exact (inP_sat_of_pEqualsNP satInNP h). Qed.

(** Cook-Levin reduces to its hardness half. *)
Theorem cookLevin_iff_satHard : CookLevin <-> SATHard.
Proof.
  split; [intros h; exact (proj2 h) | intros h; exact (conj satInNP h)].
Qed.

(** Given NP-hardness of SAT, SAT is in P exactly when P = NP. *)
Theorem inP_sat_iff_of_hard : SATHard -> (InP SAT <-> PEqualsNP).
Proof. intros hard. exact (inP_sat_iff (conj satInNP hard)). Qed.
