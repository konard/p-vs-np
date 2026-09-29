(* Issue #532, Idea 16: diagonalization and relativization.

   Rocq counterpart of ../lean/Idea16.lean; theorem names are aligned.

   Abstract part, proved for all enumerations, oracles and parameters: the
   Cantor/Turing diagonal differs from every enumerated language; the abstract
   hierarchy theorem (the diagonal of an enumerated class is decidable with
   one query to a universal evaluator but is not in the class); both arguments
   hold in every oracle world (they relativize); a relativizing technique
   cannot prove a statement that fails in some world
   (NonRelativizingIngredientFor is the generic schema of what a proof would
   have to add); and the query-complexity core of the Baker-Gill-Solovay
   oracle: every decision tree with fewer than 2^n queries errs on the test
   language for some oracle.

   Machine part, in the shared model (Complexity.v / Machines.v): oracle
   machines OMachine extend Machine by a query instruction (ostep, ORun);
   ordinary machines are oracle machines that never query (orun_lift_iff);
   against a constant oracle an oracle machine is an ordinary machine
   (run_lower_iff).  InPO, InNPO, PEqualsNPO are P^A, NP^A, P^A = NP^A, and
   for a constant oracle they are InP, InNP, PEqualsNP (inPO_const_iff,
   inNPO_const_iff, pEqualsNPO_const_iff).  BGSCollapse and BGSSeparation
   state the Baker-Gill-Solovay theorem as named premises;
   bgs_no_uniform_answer: under them neither answer holds for every oracle.
   The diagonal half of the time hierarchy is proved for machines with
   polynomial clocks (diagWithin_not_decidedWithin) and relative to every
   oracle (diagWithinO_not_decidedWithin); the hierarchies follow from the
   known universal simulations.  InDTIME, InNTIME, NTimeHierarchy: time
   classes and the nondeterministic time hierarchy (a known theorem, stated
   as a premise), with the non-vacuity theorems exists_not_inDTIME and
   exists_not_inNTIME.

   Verdict: pure diagonalization is refuted as a route to P vs NP, in full
   strength, by the published BGS theorem (bgs_no_uniform_answer).  Nothing
   here proves or refutes P = NP.

   Differences from Lean (no classical logic, no function extensionality):
   - Constructor and field names: OInstruction is obase | oquery, the table
     field of OMachine is oprogram, OVerifier is oignoreCertificate |
     opaired; Lean's OVerifier.Run, OVerifier.timeLimit, OVerifier.lower are
     overifierRun, otimeLimit, lowerVerifier.  Lean's total symbolOfIndex is
     symbolOfIndexTotal (Machines.v already has a partial symbolOfIndex), and
     Lean's List.mapIdx in lowerMachine is the index-carrying lowerRow.
   - diagLang takes a computable decoder d and a Boolean acceptance test
     instead of an injective code and a Prop decided classically: w is in
     diagLang d acc unless d w = Some m and acc m w = true.  diagonal_core
     takes the code e, its left inverse d, the relation Acc and a Boolean
     test acc equivalent to it.  DiagWithin p and DiagWithinO A p use the
     step-bounded interpreters runFor and orunFor (acceptsWithinb_iff,
     oacceptsWithinb_iff).  Since the decoders ignore trailing bits, these
     languages also diagonalize on words that merely start with a code; the
     known theorems UniversalSimulation and UniversalSimulationO are stated
     for these languages (the simulation is the same).
   - ntimeLanguage is the computable bounded certificate search
     (ntimeLanguage_iff gives the Lean meaning); the Lean anonymous DTIME
     family is dtimeLanguage.  exists_not_inDTIME and exists_not_inNTIME are
     proved by direct pointwise diagonals over decMachinePoly instead of the
     Cantor family lemma (which would need function extensionality). *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(** Generic schema over a free technique [T] (not assumed, not a
    machine-level statement): [T] is sound for the real world [real], proves
    [S], and does not relativize.  The machine-level content of the barrier
    is bgs_no_uniform_answer below. *)
Definition NonRelativizingIngredientFor (T : Technique) (real : World) (S : World -> Prop) : Prop :=
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

(* ======================================================================= *)
(** * Machine part: the barrier in the shared machine model *)

(** ** Oracle machines: a real extension of [Machine] *)

(** An oracle is a language: the query [y] is answered by [A y]. *)
Definition Oracle := Language.

(** An oracle-machine instruction: an ordinary [Instruction], or a query that
    asks the oracle about the bit word starting at the head (up to the first
    blank or separator) and moves to state [yes] or [no].  A query is one
    step. *)
Inductive OInstruction : Type :=
  | obase (i : Instruction)
  | oquery (yes no : nat).

(** An oracle machine: a finite instruction table, as for [Machine]. *)
Record OMachine := { oprogram : list (list OInstruction) }.

(** Table lookup; a missing instruction rejects, as for [Machine]. *)
Definition oinstruction (m : OMachine) (q : nat) (a : Symbol) : OInstruction :=
  match nth_error (oprogram m) q with
  | None => obase (halt false)
  | Some row => match nth_error row (symbolIndex a) with
                | None => obase (halt false) | Some i => i end
  end.

(** The query word: the bits from the head rightwards, up to the first blank
    or separator. *)
Fixpoint queryWord (s : list Symbol) : Word :=
  match s with
  | zero :: r => false :: queryWord r
  | one :: r => true :: queryWord r
  | _ => []
  end.

(** One step of an oracle machine with oracle [A]. *)
Definition ostep (A : Oracle) (m : OMachine) (c : Config) : bool + Config :=
  match oinstruction m (state c) (tapeHead c) with
  | obase (halt b) => inl b
  | obase (move next write dir) => inr (moveHead c next write dir)
  | oquery yes no =>
      inr {| state := if A (queryWord (tapeHead c :: tapeRight c)) then yes else no;
             tapeLeft := tapeLeft c; tapeHead := tapeHead c; tapeRight := tapeRight c |}
  end.

(** Halting runs of an oracle machine, with the step count (as [Run]). *)
Inductive ORun (A : Oracle) (m : OMachine) : Config -> nat -> bool -> Prop :=
| orun_halt : forall c b, ostep A m c = inl b -> ORun A m c 1 b
| orun_next : forall c c' t b, ostep A m c = inr c' ->
    ORun A m c' t b -> ORun A m c (S t) b.

Theorem orun_deterministic : forall A m c t t' b b',
  ORun A m c t b -> ORun A m c t' b' -> t = t' /\ b = b'.
Proof.
  intros A m c t t' b b' h. revert t' b'.
  induction h as [c b hs | c c' t b hs hr IH]; intros t' b' h'.
  - inversion h' as [c0 b0 hs' | c0 c0' t0 b0 hs' hr']; subst;
      rewrite hs in hs'; inversion hs'; auto.
  - inversion h' as [c0 b0 hs' | c0 c0' t0 b0 hs' hr']; subst;
      rewrite hs in hs'; inversion hs'; subst.
    destruct (IH _ _ hr') as [h1 h2]. split; [lia | exact h2].
Qed.

(** Every ordinary machine is an oracle machine that never queries. *)
Definition liftMachine (m : Machine) : OMachine :=
  {| oprogram := map (map obase) (program m) |}.

Theorem lift_instruction : forall m q a,
  oinstruction (liftMachine m) q a = obase (instruction m q a).
Proof.
  intros m q a. unfold oinstruction, liftMachine, instruction. simpl.
  rewrite nth_error_map. destruct (nth_error (program m) q) as [row |]; simpl; [| reflexivity].
  rewrite nth_error_map. destruct (nth_error row (symbolIndex a)); reflexivity.
Qed.

Theorem ostep_lift : forall A m c, ostep A (liftMachine m) c = step m c.
Proof.
  intros A m c. unfold ostep, step. rewrite lift_instruction.
  destruct (instruction m (state c) (tapeHead c)); reflexivity.
Qed.

(** Runs of a lifted machine are the runs of the machine, for every
    oracle. *)
Theorem orun_lift_iff : forall A m c t b, ORun A (liftMachine m) c t b <-> Run m c t b.
Proof.
  intros A m c t b. split; intro h.
  - induction h as [c b hs | c c' t b hs _ IH].
    + apply run_halt. rewrite <- (ostep_lift A). exact hs.
    + apply run_next with c'; [rewrite <- (ostep_lift A); exact hs | exact IH].
  - induction h as [c b hs | c c' t b hs _ IH].
    + apply orun_halt. rewrite ostep_lift. exact hs.
    + apply orun_next with c'; [rewrite ostep_lift; exact hs | exact IH].
Qed.

(** The symbol with a given column index (total; Machines.v has the partial
    [symbolOfIndex]). *)
Definition symbolOfIndexTotal (i : nat) : Symbol :=
  match i with 0 => blank | 1 => zero | 2 => one | _ => separator end.

Theorem symbolOfIndexTotal_index : forall a, symbolOfIndexTotal (symbolIndex a) = a.
Proof. intro a. destruct a; reflexivity. Qed.

(** Against the constant oracle [fun _ => b], a query is an ordinary move that
    rewrites the scanned symbol and does not move. *)
Definition lowerInstruction (b : bool) (a : Symbol) (oi : OInstruction) : Instruction :=
  match oi with
  | obase i => i
  | oquery yes no => move (if b then yes else no) a stay
  end.

(** A row of the lowered table; [k] is the column index of the first entry. *)
Fixpoint lowerRow (b : bool) (k : nat) (row : list OInstruction) : list Instruction :=
  match row with
  | [] => []
  | oi :: r => lowerInstruction b (symbolOfIndexTotal k) oi :: lowerRow b (S k) r
  end.

Lemma nth_error_lowerRow : forall b row k n,
  nth_error (lowerRow b k row) n =
  option_map (lowerInstruction b (symbolOfIndexTotal (k + n))) (nth_error row n).
Proof.
  intros b row. induction row as [| oi r IH]; intros k n; destruct n as [| n]; simpl;
    try reflexivity.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

(** The ordinary machine that simulates [m] against the constant oracle
    [fun _ => b]. *)
Definition lowerMachine (b : bool) (m : OMachine) : Machine :=
  {| program := map (lowerRow b 0) (oprogram m) |}.

Theorem lower_instruction : forall b m q a,
  instruction (lowerMachine b m) q a = lowerInstruction b a (oinstruction m q a).
Proof.
  intros b m q a. unfold instruction, oinstruction, lowerMachine. simpl.
  rewrite nth_error_map. destruct (nth_error (oprogram m) q) as [row |]; simpl; [| reflexivity].
  rewrite nth_error_lowerRow. simpl.
  destruct (nth_error row (symbolIndex a)); simpl; [| reflexivity].
  rewrite symbolOfIndexTotal_index. reflexivity.
Qed.

Theorem step_lower : forall b m c, step (lowerMachine b m) c = ostep (fun _ => b) m c.
Proof.
  intros b m c. unfold step, ostep. rewrite lower_instruction.
  destruct (oinstruction m (state c) (tapeHead c)) as [[r | q w d] | y n]; reflexivity.
Qed.

(** Runs against a constant oracle are runs of an ordinary machine. *)
Theorem run_lower_iff : forall b m c t r,
  Run (lowerMachine b m) c t r <-> ORun (fun _ => b) m c t r.
Proof.
  intros b m c t r. split; intro h.
  - induction h as [c r hs | c c' t r hs _ IH].
    + apply orun_halt. rewrite <- step_lower. exact hs.
    + apply orun_next with c'; [rewrite <- step_lower; exact hs | exact IH].
  - induction h as [c r hs | c c' t r hs _ IH].
    + apply run_halt. rewrite step_lower. exact hs.
    + apply run_next with c'; [rewrite step_lower; exact hs | exact IH].
Qed.

(** ** Oracle classes P^A, NP^A *)

(** [m] decides [L] with oracle [A] within the polynomial [p]. *)
Definition ODecidesWithin (A : Oracle) (m : OMachine) (p : Polynomial) (L : Language) : Prop :=
  forall x, exists t b, t <= evalPoly p (length x) /\ ORun A m (initial x) t b /\ b = L x.

(** [L] is in P^A. *)
Definition InPO (A : Oracle) (L : Language) : Prop :=
  exists (m : OMachine) (p : Polynomial), ODecidesWithin A m p L.

(** Oracle verifiers, mirroring [VerifierProgram]. *)
Inductive OVerifier : Type :=
  | oignoreCertificate (m : OMachine)
  | opaired (m : OMachine).

Definition overifierRun (v : OVerifier) (A : Oracle) (x cert : Word) (t : nat) (b : bool)
    : Prop :=
  match v with
  | oignoreCertificate m => ORun A m (initial x) t b
  | opaired m => ORun A m (pairedInput x cert) t b
  end.

Definition otimeLimit (v : OVerifier) (p : Polynomial) (x cert : Word) : nat :=
  match v with
  | oignoreCertificate _ => evalPoly p (length x)
  | opaired _ => evalPoly p (length x + length cert + 1)
  end.

(** [L] is in NP^A: the fields of [ClassNP], with an oracle verifier. *)
Definition InNPO (A : Oracle) (L : Language) : Prop :=
  exists (v : OVerifier) (timeBound certBound : Polynomial),
    (forall x cert, length cert <= evalPoly certBound (length x) ->
       exists t b, t <= otimeLimit v timeBound x cert /\ overifierRun v A x cert t b) /\
    forall x, L x = true <-> exists cert t, length cert <= evalPoly certBound (length x) /\
      t <= otimeLimit v timeBound x cert /\ overifierRun v A x cert t true.

(** P^A = NP^A. *)
Definition PEqualsNPO (A : Oracle) : Prop := forall L, InNPO A L -> InPO A L.

(** P is contained in P^A for every oracle. *)
Theorem inPO_of_inP : forall A L, InP L -> InPO A L.
Proof.
  intros A L h. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  exists (liftMachine m), p. intro x. destruct (hm x) as [t [b [ht [hr hb]]]].
  exists t, b. split; [exact ht | split; [apply orun_lift_iff; exact hr | exact hb]].
Qed.

(** P^A = P for a constant oracle: oracle machines are ordinary machines. *)
Theorem inPO_const_iff : forall (b : bool) L, InPO (fun _ => b) L <-> InP L.
Proof.
  intros b L. split.
  - intros [m [p hm]]. apply (inP_of_decidesWithin (lowerMachine b m) p). intro x.
    destruct (hm x) as [t [r [ht [hr hb]]]]. exists t, r.
    split; [exact ht | split; [apply run_lower_iff; exact hr | exact hb]].
  - apply inPO_of_inP.
Qed.

(** P^A is contained in NP^A for every oracle. *)
Theorem inNPO_of_inPO : forall A L, InPO A L -> InNPO A L.
Proof.
  intros A L [m [p hm]].
  exists (oignoreCertificate m), p, {| coefficient := 0; degree := 0 |}. split.
  - intros x cert _. destruct (hm x) as [t [b [ht [hr _]]]]. exists t, b. split; assumption.
  - intro x. destruct (hm x) as [t [b [ht [hr hb]]]]. split.
    + intro hx. exists [], t. split; [simpl; lia | split; [exact ht |]].
      subst b. rewrite hx in hr. exact hr.
    + intros [cert [t' [_ [_ hr']]]].
      destruct (orun_deterministic _ _ _ _ _ _ _ hr hr') as [_ hbt].
      rewrite <- hb. exact hbt.
Qed.

Definition liftVerifier (v : VerifierProgram) : OVerifier :=
  match v with
  | ignoreCertificate m => oignoreCertificate (liftMachine m)
  | paired m => opaired (liftMachine m)
  end.

Definition lowerVerifier (b : bool) (v : OVerifier) : VerifierProgram :=
  match v with
  | oignoreCertificate m => ignoreCertificate (lowerMachine b m)
  | opaired m => paired (lowerMachine b m)
  end.

Theorem liftVerifier_run : forall A v x cert t r,
  overifierRun (liftVerifier v) A x cert t r <-> verifierRun v x cert t r.
Proof. intros A [m | m] x cert t r; apply orun_lift_iff. Qed.

Theorem liftVerifier_timeLimit : forall v p x cert,
  otimeLimit (liftVerifier v) p x cert = timeLimit v p x cert.
Proof. intros [m | m] p x cert; reflexivity. Qed.

Theorem lower_run : forall b v x cert t r,
  verifierRun (lowerVerifier b v) x cert t r <-> overifierRun v (fun _ => b) x cert t r.
Proof. intros b [m | m] x cert t r; apply run_lower_iff. Qed.

Theorem lower_timeLimit : forall b v p x cert,
  timeLimit (lowerVerifier b v) p x cert = otimeLimit v p x cert.
Proof. intros b [m | m] p x cert; reflexivity. Qed.

(** NP is contained in NP^A for every oracle. *)
Theorem inNPO_of_inNP : forall A L, InNP L -> InNPO A L.
Proof.
  intros A L [N <-].
  exists (liftVerifier (np_verifier N)), (np_timeBound N), (np_certBound N). split.
  - intros x cert hc. destruct (np_terminates N x cert hc) as [t [b [ht hr]]].
    exists t, b. split; [rewrite liftVerifier_timeLimit; exact ht | apply liftVerifier_run; exact hr].
  - intro x. split.
    + intro hx. apply (np_correct N x) in hx. destruct hx as [cert [t [hc [ht hr]]]].
      exists cert, t. split; [exact hc | split].
      * rewrite liftVerifier_timeLimit. exact ht.
      * apply liftVerifier_run. exact hr.
    + intros [cert [t [hc [ht hr]]]]. apply (np_correct N x). exists cert, t.
      split; [exact hc | split].
      * rewrite <- (liftVerifier_timeLimit (np_verifier N)). exact ht.
      * apply (liftVerifier_run A). exact hr.
Qed.

(** NP^A = NP for a constant oracle. *)
Theorem inNPO_const_iff : forall (b : bool) L, InNPO (fun _ => b) L <-> InNP L.
Proof.
  intros b L. split.
  - intros [v [tb [cb [hterm hcorr]]]].
    unshelve eexists {| np_language := L; np_verifier := lowerVerifier b v;
                        np_timeBound := tb; np_certBound := cb |}; [| | reflexivity].
    + intros x cert hc. destruct (hterm x cert hc) as [t [r [ht hr]]].
      exists t, r. split; [rewrite lower_timeLimit; exact ht | apply lower_run; exact hr].
    + intro x. split.
      * intro hx. apply hcorr in hx. destruct hx as [cert [t [hc [ht hr]]]].
        exists cert, t. split; [exact hc | split].
        -- rewrite lower_timeLimit. exact ht.
        -- apply lower_run. exact hr.
      * intros [cert [t [hc [ht hr]]]]. apply hcorr. exists cert, t.
        split; [exact hc | split].
        -- rewrite <- (lower_timeLimit b). exact ht.
        -- apply (lower_run b). exact hr.
  - apply inNPO_of_inNP.
Qed.

(** The unrelativized question is the instance of a constant (for example the
    empty) oracle. *)
Theorem pEqualsNPO_const_iff : forall b : bool, PEqualsNPO (fun _ => b) <-> PEqualsNP.
Proof.
  intro b. split.
  - intros h L hL. apply (inPO_const_iff b L). apply h. apply (inNPO_const_iff b L). exact hL.
  - intros h L hL. apply (inPO_const_iff b L). apply h. apply (inNPO_const_iff b L). exact hL.
Qed.

(** A relativizing proof of P = NP (one valid for every oracle) proves
    P = NP. *)
Theorem pEqualsNP_of_all_oracles : (forall A, PEqualsNPO A) -> PEqualsNP.
Proof. intro h. exact (proj1 (pEqualsNPO_const_iff false) (h _)). Qed.

(** A relativizing proof of P <> NP proves P <> NP. *)
Theorem pNotEqualsNP_of_all_oracles : (forall A, ~ PEqualsNPO A) -> PNotEqualsNP.
Proof. intros h hP. exact (h (fun _ => false) (proj2 (pEqualsNPO_const_iff false) hP)). Qed.

(** ** Baker-Gill-Solovay, stated in this model *)

(** Known theorem, not mechanised here (Baker, Gill, Solovay, "Relativizations
    of the P =? NP question", SIAM J. Comput. 4(4), 1975): there is an oracle
    [A] with P^A = NP^A (for example a PSPACE-complete language). *)
Definition BGSCollapse : Prop := exists A : Oracle, PEqualsNPO A.

(** Known theorem, not mechanised here (Baker, Gill, Solovay 1975): there is
    an oracle [B] with P^B <> NP^B.  Its query-complexity core is
    oracle_adversary. *)
Definition BGSSeparation : Prop := exists B : Oracle, ~ PEqualsNPO B.

(** The barrier.  Given BGS, neither answer to P vs NP holds relative to
    every oracle, so no argument that is valid for every oracle settles P vs
    NP. *)
Theorem bgs_no_uniform_answer : BGSCollapse -> BGSSeparation ->
  ~ (forall A, PEqualsNPO A) /\ ~ (forall A, ~ PEqualsNPO A).
Proof.
  intros [A hA] [B hB]. split.
  - intro h. exact (hB (h B)).
  - intro h. exact (h A hA).
Qed.

(** ** The diagonal half of the time hierarchy, in the machine model *)

(** The diagonal language of a family with a computable decoder [d] and a
    Boolean acceptance test [acc]: [w] is in it unless [w] decodes to a
    member accepting [w]. *)
Definition diagLang {M : Type} (d : Word -> option M) (acc : M -> Word -> bool) : Language :=
  fun w => match d w with Some m => negb (acc m w) | None => true end.

(** Diagonal core.  No member of the family accepts exactly [diagLang]. *)
Theorem diagonal_core : forall {M : Type} (e : M -> Word) (d : Word -> option M),
  (forall a, d (e a) = Some a) ->
  forall (Acc : M -> Word -> Prop) (acc : M -> Word -> bool),
  (forall m w, acc m w = true <-> Acc m w) ->
  forall m, ~ forall w, Acc m w <-> diagLang d acc w = true.
Proof.
  intros M e d hd Acc acc hacc m h.
  destruct (h (e m)) as [h1 h2]. unfold diagLang in h1, h2. rewrite hd in h1, h2.
  destruct (acc m (e m)) eqn:ha.
  - pose proof (h1 (proj1 (hacc m (e m)) ha)) as hf. simpl in hf. discriminate.
  - assert (hA : Acc m (e m)) by (apply h2; reflexivity).
    apply hacc in hA. rewrite ha in hA. discriminate.
Qed.

(** Clocked acceptance: [m] accepts [w] within [p(|w|)] steps. *)
Definition AcceptsWithin (m : Machine) (p : Polynomial) (w : Word) : Prop :=
  exists t, t <= evalPoly p (length w) /\ Run m (initial w) t true.

(** The computable test for [AcceptsWithin] (step-bounded interpreter). *)
Definition acceptsWithinb (m : Machine) (p : Polynomial) (w : Word) : bool :=
  match runFor m (initial w) (evalPoly p (length w)) with
  | Some true => true
  | _ => false
  end.

Theorem acceptsWithinb_iff : forall m p w, acceptsWithinb m p w = true <-> AcceptsWithin m p w.
Proof.
  intros m p w. unfold acceptsWithinb. split.
  - destruct (runFor m (initial w) (evalPoly p (length w))) as [[|] |] eqn:hr; intro h;
      try discriminate.
    destruct (run_of_runFor _ _ _ _ hr) as [t [ht hrun]]. exists t. auto.
  - intros [t [ht hrun]]. rewrite (runFor_of_run _ _ _ _ hrun _ ht). reflexivity.
Qed.

(** The clocked diagonal language for the time bound [p]. *)
Definition DiagWithin (p : Polynomial) : Language :=
  diagLang decMachine (fun m w => acceptsWithinb m p w).

Theorem acceptsWithin_iff_of_decidesWithin : forall m p L, DecidesWithin m p L ->
  forall w, AcceptsWithin m p w <-> L w = true.
Proof.
  intros m p L h w. destruct (h w) as [t [b [ht [hr hb]]]]. split.
  - intros [t' [_ hr']]. destruct (run_deterministic _ _ _ _ _ _ hr hr') as [_ hbt].
    rewrite <- hb. exact hbt.
  - intro hL. exists t. split; [exact ht |]. subst b. rewrite hL in hr. exact hr.
Qed.

(** Diagonal half of the deterministic time hierarchy (proved).  No machine
    decides [DiagWithin p] within the time bound [p]. *)
Theorem diagWithin_not_decidedWithin : forall p : Polynomial,
  ~ exists m, DecidesWithin m p (DiagWithin p).
Proof.
  intros p [m hm].
  exact (diagonal_core encMachine decMachine decMachine_encMachine
    (fun m w => AcceptsWithin m p w) (fun m w => acceptsWithinb m p w)
    (fun m w => acceptsWithinb_iff m p w) m
    (acceptsWithin_iff_of_decidesWithin m p _ hm)).
Qed.

(** Known theorem, not mechanised here (clocked universal simulation:
    Hartmanis-Stearns, "On the computational complexity of algorithms", Trans.
    AMS 117, 1965; Hennie-Stearns, J. ACM 13(4), 1966): for each polynomial
    [p], a machine can decode a machine [m] from the front of [w] and simulate
    [m] on [w] for [p(|w|)] steps in polynomial time, so [DiagWithin p] is in
    P. *)
Definition UniversalSimulation : Prop := forall p : Polynomial, InP (DiagWithin p).

(** The deterministic time hierarchy for polynomial bounds, in the machine
    model: no single polynomial bounds the running time of all of P. *)
Definition TimeHierarchy : Prop :=
  forall p : Polynomial, exists L : Language, InP L /\ ~ exists m, DecidesWithin m p L.

(** The time hierarchy follows from the proved diagonal half and universal
    simulation. *)
Theorem timeHierarchy_of_universalSimulation : UniversalSimulation -> TimeHierarchy.
Proof.
  intros h p. exists (DiagWithin p). split; [exact (h p) | exact (diagWithin_not_decidedWithin p)].
Qed.

(** Consequence: P has no uniform polynomial time bound. *)
Theorem no_uniform_bound_of_timeHierarchy : TimeHierarchy ->
  ~ exists p : Polynomial, forall L, InP L -> exists m, DecidesWithin m p L.
Proof.
  intros h [p hp]. destruct (h p) as [L [hL hn]]. exact (hn (hp L hL)).
Qed.

(** ** The diagonal half relative to every oracle *)

Definition encOInstruction (oi : OInstruction) : Word :=
  match oi with
  | obase i => false :: encInstruction i
  | oquery yes no => true :: (encNat yes ++ encNat no)
  end.

Theorem encOInstruction_prefixFree : PrefixFree encOInstruction.
Proof.
  intros a b r s h. destruct a as [i | y n], b as [j | y' n']; simpl in h; try discriminate.
  - injection h as h. destruct (encInstruction_prefixFree _ _ _ _ h) as [-> ->]. auto.
  - injection h as h. rewrite <- !app_assoc in h.
    destruct (encNat_prefixFree _ _ _ _ h) as [-> h1].
    destruct (encNat_prefixFree _ _ _ _ h1) as [-> ->]. auto.
Qed.

(** The code of an oracle machine. *)
Definition encOMachine (m : OMachine) : Word := encList (encList encOInstruction) (oprogram m).

Theorem encOMachine_injective : forall m m', encOMachine m = encOMachine m' -> m = m'.
Proof.
  intros [p] [p'] h. unfold encOMachine in h. simpl in h.
  assert (h' : encList (encList encOInstruction) p ++ [] =
               encList (encList encOInstruction) p' ++ []) by (rewrite h; reflexivity).
  destruct (encList_prefixFree _ (encList_prefixFree _ encOInstruction_prefixFree)
              _ _ _ _ h') as [-> _].
  reflexivity.
Qed.

(** Computable decoders for oracle machines (trailing bits are ignored). *)
Definition decOInstruction (w : Word) : option (OInstruction * Word) :=
  match w with
  | false :: r => obind (decInstruction r) (fun '(i, r1) => Some (obase i, r1))
  | true :: r =>
      obind (decNat r) (fun '(y, r1) =>
      obind (decNat r1) (fun '(n, r2) => Some (oquery y n, r2)))
  | [] => None
  end.

Theorem decOInstruction_encOInstruction : forall oi r,
  decOInstruction (encOInstruction oi ++ r) = Some (oi, r).
Proof.
  intros [i | y n] r; simpl.
  - rewrite decInstruction_encInstruction. reflexivity.
  - rewrite <- app_assoc, decNat_encNat. simpl. rewrite decNat_encNat. reflexivity.
Qed.

Definition decOMachine (w : Word) : option OMachine :=
  obind (decList (decList decOInstruction) w) (fun '(p, _) => Some {| oprogram := p |}).

Theorem decOMachine_encOMachine : forall m, decOMachine (encOMachine m) = Some m.
Proof.
  intros [p]. unfold decOMachine, encOMachine. simpl.
  rewrite <- (app_nil_r (encList (encList encOInstruction) p)).
  rewrite (decList_encList (encList encOInstruction) (decList decOInstruction)).
  - reflexivity.
  - apply decList_encList. apply decOInstruction_encOInstruction.
Qed.

(** A step-bounded interpreter for oracle machines. *)
Fixpoint orunFor (A : Oracle) (m : OMachine) (c : Config) (fuel : nat) : option bool :=
  match fuel with
  | 0 => None
  | S f => match ostep A m c with
           | inl b => Some b
           | inr c' => orunFor A m c' f
           end
  end.

Theorem orunFor_of_orun : forall A m c t b, ORun A m c t b ->
  forall fuel, t <= fuel -> orunFor A m c fuel = Some b.
Proof.
  intros A m c t b h. induction h as [c b hs | c c' t b hs _ IH]; intros fuel hf;
    (destruct fuel as [| fuel]; [lia |]); simpl; rewrite hs; [reflexivity |].
  apply IH. lia.
Qed.

Theorem orun_of_orunFor : forall A m fuel c b, orunFor A m c fuel = Some b ->
  exists t, t <= fuel /\ ORun A m c t b.
Proof.
  intros A m fuel. induction fuel as [| fuel IH]; intros c b h; simpl in h; [discriminate |].
  destruct (ostep A m c) as [b' | c'] eqn:hs.
  - injection h as <-. exists 1. split; [lia | apply orun_halt; exact hs].
  - destruct (IH _ _ h) as [t [ht hr]]. exists (S t).
    split; [lia | apply orun_next with c'; assumption].
Qed.

(** Clocked acceptance relative to the oracle [A]. *)
Definition OAcceptsWithin (A : Oracle) (m : OMachine) (p : Polynomial) (w : Word) : Prop :=
  exists t, t <= evalPoly p (length w) /\ ORun A m (initial w) t true.

Definition oacceptsWithinb (A : Oracle) (m : OMachine) (p : Polynomial) (w : Word) : bool :=
  match orunFor A m (initial w) (evalPoly p (length w)) with
  | Some true => true
  | _ => false
  end.

Theorem oacceptsWithinb_iff : forall A m p w,
  oacceptsWithinb A m p w = true <-> OAcceptsWithin A m p w.
Proof.
  intros A m p w. unfold oacceptsWithinb. split.
  - destruct (orunFor A m (initial w) (evalPoly p (length w))) as [[|] |] eqn:hr; intro h;
      try discriminate.
    destruct (orun_of_orunFor _ _ _ _ _ hr) as [t [ht hrun]]. exists t. auto.
  - intros [t [ht hrun]]. rewrite (orunFor_of_orun _ _ _ _ _ hrun _ ht). reflexivity.
Qed.

(** The clocked diagonal language relative to [A]. *)
Definition DiagWithinO (A : Oracle) (p : Polynomial) : Language :=
  diagLang decOMachine (fun m w => oacceptsWithinb A m p w).

(** The diagonal half relativizes (proved for every oracle).  No oracle
    machine decides [DiagWithinO A p] with oracle [A] within [p]. *)
Theorem diagWithinO_not_decidedWithin : forall (A : Oracle) (p : Polynomial),
  ~ exists m, ODecidesWithin A m p (DiagWithinO A p).
Proof.
  intros A p [m hm].
  refine (diagonal_core encOMachine decOMachine decOMachine_encOMachine
    (fun m w => OAcceptsWithin A m p w) (fun m w => oacceptsWithinb A m p w)
    (fun m w => oacceptsWithinb_iff A m p w) m _).
  intro w. destruct (hm w) as [t [b [ht [hr hb]]]]. split.
  - intros [t' [_ hr']]. destruct (orun_deterministic _ _ _ _ _ _ _ hr hr') as [_ hbt].
    rewrite hbt in hb. exact (eq_sym hb).
  - intro hL. exists t. split; [exact ht |].
    assert (hbt : b = true) by (rewrite hb; exact hL).
    rewrite hbt in hr. exact hr.
Qed.

(** The time hierarchy relative to [A]. *)
Definition TimeHierarchyO (A : Oracle) : Prop :=
  forall p : Polynomial, exists L : Language, InPO A L /\ ~ exists m, ODecidesWithin A m p L.

(** Known theorem, not mechanised here (the universal simulation of
    Hartmanis-Stearns 1965 makes the same queries as the simulated machine;
    see Baker, Gill, Solovay 1975, Section 1): for each oracle [A] and
    polynomial [p], [DiagWithinO A p] is in P^A. *)
Definition UniversalSimulationO : Prop :=
  forall (A : Oracle) (p : Polynomial), InPO A (DiagWithinO A p).

(** The time hierarchy holds relative to every oracle: it is a relativizing
    theorem, which is why it cannot settle P vs NP (bgs_no_uniform_answer). *)
Theorem timeHierarchyO_of_universalSimulationO : UniversalSimulationO ->
  forall A, TimeHierarchyO A.
Proof.
  intros h A p. exists (DiagWithinO A p).
  split; [exact (h A p) | exact (diagWithinO_not_decidedWithin A p)].
Qed.

(** ** Time classes and the nondeterministic time hierarchy

    [T : nat -> nat] is an arbitrary time function; [c] absorbs constant
    factors. *)

(** [L] is in DTIME(T): a machine decides [L] within [c * T(|x|) + c]
    steps. *)
Definition InDTIME (T : nat -> nat) (L : Language) : Prop :=
  exists (m : Machine) (c : nat), forall x, exists t b,
    t <= c * T (length x) + c /\ Run m (initial x) t b /\ b = L x.

(** [L] is in NTIME(T), in the verifier form of [ClassNP]: a machine reading
    [pairedInput x cert] halts within [c * T(|x|) + c] steps on every
    certificate of length at most [c * T(|x|) + c], and [x] is in [L] iff
    some such certificate is accepted. *)
Definition InNTIME (T : nat -> nat) (L : Language) : Prop :=
  exists (m : Machine) (c : nat),
    (forall x cert, length cert <= c * T (length x) + c ->
       exists t b, t <= c * T (length x) + c /\ Run m (pairedInput x cert) t b) /\
    forall x, L x = true <-> exists cert t, length cert <= c * T (length x) + c /\
      t <= c * T (length x) + c /\ Run m (pairedInput x cert) t true.

(** A separation of nondeterministic time classes: NTIME(T2) is not
    contained in NTIME(T1). *)
Definition NTimeHierarchyGap (T1 T2 : nat -> nat) : Prop :=
  exists L, InNTIME T2 L /\ ~ InNTIME T1 L.

(** Known theorem, not mechanised here (nondeterministic time hierarchy:
    Cook, "A hierarchy for nondeterministic time complexity", JCSS 7(4), 1973;
    Seiferas-Fischer-Meyer, J. ACM 25(1), 1978; Zak, TCS 21(3), 1983), in the
    form used by Williams' ACC lower bound: NTIME(2^n) is not contained in
    NTIME(2^n / (n+1)^k) for every k >= 3.  The published proofs are for
    multitape machines; the polynomial gap (n+1)^k with k >= 3 leaves room for
    the O(|M| T) overhead of one-tape universal simulation in this one-tape
    verifier model. *)
Definition NTimeHierarchy : Prop :=
  forall k : nat, 3 <= k -> NTimeHierarchyGap (fun n => 2 ^ n / (n + 1) ^ k) (fun n => 2 ^ n).

(** All words of length at most [n]. *)
Definition wordsUpTo (n : nat) : list Word := flat_map allAssignments (seq 0 (S n)).

Lemma mem_wordsUpTo : forall n (w : Word), In w (wordsUpTo n) <-> length w <= n.
Proof.
  intros n w. unfold wordsUpTo. split; intro h.
  - apply in_flat_map in h. destruct h as [k [hk hw]].
    apply in_seq in hk. apply mem_allAssignments_iff in hw. lia.
  - apply in_flat_map. exists (length w).
    split; [apply in_seq; lia | apply mem_allAssignments_iff; reflexivity].
Qed.

(** The language accepted by the verifier [fst x] with constant
    [coefficient (snd x)]: a computable bounded search over certificates. *)
Definition ntimeLanguage (T : nat -> nat) (x : Machine * Polynomial) : Language := fun w =>
  let B := coefficient (snd x) * T (length w) + coefficient (snd x) in
  existsb (fun cert => match runFor (fst x) (pairedInput w cert) B with
                       | Some true => true
                       | _ => false
                       end) (wordsUpTo B).

Theorem ntimeLanguage_iff : forall T x w, ntimeLanguage T x w = true <->
  exists cert t, length cert <= coefficient (snd x) * T (length w) + coefficient (snd x) /\
    t <= coefficient (snd x) * T (length w) + coefficient (snd x) /\
    Run (fst x) (pairedInput w cert) t true.
Proof.
  intros T x w. unfold ntimeLanguage. cbv zeta. split.
  - intro h. apply existsb_exists in h. destruct h as [cert [hc hr]].
    destruct (runFor (fst x) (pairedInput w cert) _) as [[|] |] eqn:hrun; try discriminate.
    destruct (run_of_runFor _ _ _ _ hrun) as [t [ht hrt]].
    exists cert, t. split; [apply mem_wordsUpTo; exact hc | auto].
  - intros [cert [t [hc [ht hr]]]]. apply existsb_exists. exists cert.
    split; [apply mem_wordsUpTo; exact hc |].
    rewrite (runFor_of_run _ _ _ _ hr _ ht). reflexivity.
Qed.

(** Non-vacuity: every NTIME(T) misses some language (direct pointwise
    diagonal over [decMachinePoly]). *)
Theorem exists_not_inNTIME : forall T : nat -> nat, exists L, ~ InNTIME T L.
Proof.
  intro T.
  exists (fun w => match decMachinePoly w with
                   | Some x => negb (ntimeLanguage T x w)
                   | None => true
                   end).
  intros [m [c [_ hc]]].
  set (x := (m, {| coefficient := c; degree := 0 |})).
  pose proof (hc (encMachinePoly x)) as h. cbv beta in h.
  rewrite decMachinePoly_encMachinePoly in h.
  pose proof (ntimeLanguage_iff T x (encMachinePoly x)) as hn.
  destruct (ntimeLanguage T x (encMachinePoly x)).
  - pose proof (proj2 h (proj1 hn eq_refl)) as hf. simpl in hf. discriminate.
  - pose proof (proj2 hn (proj1 h eq_refl)) as hf. discriminate.
Qed.

(** The language decided by the machine [fst x] within
    [coefficient (snd x) * T(|w|) + coefficient (snd x)] steps (computable). *)
Definition dtimeLanguage (T : nat -> nat) (x : Machine * Polynomial) : Language := fun w =>
  match runFor (fst x) (initial w) (coefficient (snd x) * T (length w) + coefficient (snd x)) with
  | Some true => true
  | _ => false
  end.

Theorem dtimeLanguage_eq : forall T m c w t b,
  t <= c * T (length w) + c -> Run m (initial w) t b ->
  dtimeLanguage T (m, {| coefficient := c; degree := 0 |}) w = b.
Proof.
  intros T m c w t b ht hr.
  change (match runFor m (initial w) (c * T (length w) + c) with
          | Some true => true | _ => false end = b).
  rewrite (runFor_of_run _ _ _ _ hr _ ht). destruct b; reflexivity.
Qed.

(** Non-vacuity: every DTIME(T) misses some language (direct pointwise
    diagonal over [decMachinePoly]). *)
Theorem exists_not_inDTIME : forall T : nat -> nat, exists L, ~ InDTIME T L.
Proof.
  intro T.
  exists (fun w => match decMachinePoly w with
                   | Some x => negb (dtimeLanguage T x w)
                   | None => true
                   end).
  intros [m [c hm]].
  set (x := (m, {| coefficient := c; degree := 0 |})).
  destruct (hm (encMachinePoly x)) as [t [b [ht [hr hb]]]]. cbv beta in hb.
  rewrite decMachinePoly_encMachinePoly in hb.
  assert (hd : dtimeLanguage T x (encMachinePoly x) = b)
    by exact (dtimeLanguage_eq T m c _ t b ht hr).
  rewrite hd in hb.
  destruct b; discriminate.
Qed.
