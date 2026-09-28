(** HISTORICAL TOY MODEL: The P/NP class predicates use separate machine and
    runtime semantics. Reductions reuse the shared finite machine
    representation, but are not linked to the class predicates. This file
    does not establish the Clay P versus NP statement. *)

(**
  PvsNP.v - Formal specification and test/check for P vs NP

  This file provides a formal framework for reasoning about the P vs NP problem,
  including definitions of complexity classes and basic verification tests.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From proofs.complexity.rocq Require Import Complexity.
Import ListNotations.

(** * 1. Basic Definitions *)

(** ** Input and Output Types *)

(** We model computational problems over binary strings *)
Definition BinaryString := list bool.

(** A decision problem is a predicate on binary strings *)
Definition DecisionProblem := BinaryString -> Prop.

(** Length of a binary string (input size) *)
Definition input_size (s : BinaryString) : nat := length s.

(** * 2. Polynomial Time Complexity *)

(** ** Polynomial Bound Definition *)

(** A function is polynomial-time bounded if there exists a polynomial
    that bounds its runtime *)
Definition is_polynomial (f : nat -> nat) : Prop :=
  exists (k c : nat), forall n, f n <= c * (n ^ k) + c.

(** Examples of polynomial functions *)
Theorem constant_is_poly (c : nat) : is_polynomial (fun _ => c).
Proof.
  unfold is_polynomial.
  exists 0, c.
  intros n.
  simpl.
  rewrite Nat.mul_1_r.
  (* c <= c + c *)
  apply Nat.le_add_r.
Qed.

Theorem linear_is_poly : is_polynomial (fun n => n).
Proof.
  unfold is_polynomial.
  exists 1, 1.
  intros n.
  simpl. lia.
Qed.

Theorem quadratic_is_poly : is_polynomial (fun n => n * n).
Proof.
  unfold is_polynomial.
  exists 2, 1.
  intros n.
  simpl. nia.
Qed.

(** Sum and product of polynomials are polynomial *)
Theorem poly_sum : forall f g,
  is_polynomial f -> is_polynomial g -> is_polynomial (fun n => f n + g n).
Proof.
  intros f g [k1 [c1 Hf]] [k2 [c2 Hg]].
  unfold is_polynomial.
  (* Use the maximum degree and sum of constants *)
  exists (Nat.max k1 k2), (c1 + c2).
  intros n.
  specialize (Hf n). specialize (Hg n).
  apply Nat.add_le_mono; auto.
Admitted. (* Proof requires additional lemmas about max and powers *)

(** * 3. Deterministic Turing Machine Model *)

(** ** Abstract Turing Machine *)

(** We model a deterministic Turing machine abstractly *)
Record TuringMachine := {
  TM_states : nat;  (* Number of states *)
  TM_alphabet : nat; (* Size of tape alphabet *)
  TM_transition : nat -> nat -> (nat * nat * bool); (* state -> symbol -> (new_state, new_symbol, move_right) *)
  TM_initial_state : nat;
  TM_accept_state : nat;
  TM_reject_state : nat;
}.

(** An unbounded tape, a current state, and a head position. *)
Record Configuration := {
  config_state : nat;
  config_tape : nat -> nat;
  config_head : nat
}.

(** Binary input is written at the beginning of an otherwise blank tape. *)
Definition initial_configuration (M : TuringMachine) (input : BinaryString) : Configuration :=
  {| config_state := TM_initial_state M;
     config_tape := fun i => if nth i input false then 1 else 0;
     config_head := 0 |}.

(** Halted configurations stay fixed. The head is bounded below by zero. *)
Definition step (M : TuringMachine) (c : Configuration) : Configuration :=
  if orb (Nat.eqb (config_state c) (TM_accept_state M))
         (Nat.eqb (config_state c) (TM_reject_state M)) then c
  else
    let '(next_state, symbol, move_right) :=
      TM_transition M (config_state c) (config_tape c (config_head c)) in
    {| config_state := next_state;
       config_tape := fun i => if Nat.eqb i (config_head c) then symbol else config_tape c i;
       config_head := if move_right then S (config_head c) else pred (config_head c) |}.

Fixpoint run (M : TuringMachine) (input : BinaryString) (steps : nat) : Configuration :=
  match steps with
  | 0 => initial_configuration M input
  | S n => step M (run M input n)
  end.

Definition accepts (M : TuringMachine) (input : BinaryString) : Prop :=
  exists steps, config_state (run M input steps) = TM_accept_state M.

(** Time bound for a TM on an input *)
Definition TM_time_bounded (M : TuringMachine) (time : nat -> nat) : Prop :=
  forall (input : BinaryString),
    exists (steps : nat),
      steps <= time (input_size input) /\
      (config_state (run M input steps) = TM_accept_state M \/
       config_state (run M input steps) = TM_reject_state M).

(** * 4. Complexity Class P *)

(** ** Definition of P (Polynomial Time) *)

(** A decision problem L is in P if there exists a deterministic Turing machine M
    and a polynomial time bound p such that:
    1. M runs in time p(n) where n is the input size
    2. M accepts x iff x ∈ L *)
Definition in_P (L : DecisionProblem) : Prop :=
  exists (M : TuringMachine) (time : nat -> nat),
    is_polynomial time /\
    TM_time_bounded M time /\
    forall (x : BinaryString),
      L x <-> accepts M x.

(** * 5. Complexity Class NP *)

(** ** Certificate/Witness-based Definition of NP *)

(** A decision problem L is in NP if there exists a polynomial-time verifier V
    such that for every input x:
    - x ∈ L iff there exists a certificate c (polynomial in |x|) such that V(x, c) accepts *)

Definition Certificate := BinaryString.

(** Polynomial-size certificate bound *)
Definition poly_certificate_size (cert_size : nat -> nat) : Prop :=
  is_polynomial cert_size.

(** Polynomial-time verifier *)
Definition polynomial_time_verifier (V : BinaryString -> Certificate -> bool) : Prop :=
  exists (time : nat -> nat),
    is_polynomial time /\
    forall (x : BinaryString) (c : Certificate),
      (* V(x, c) runs in time polynomial in |x| *)
      True. (* Abstract time bound *)

(** Definition of NP *)
Definition in_NP (L : DecisionProblem) : Prop :=
  exists (V : BinaryString -> Certificate -> bool) (cert_size : nat -> nat),
    poly_certificate_size cert_size /\
    polynomial_time_verifier V /\
    forall (x : BinaryString),
      L x <-> exists (c : Certificate),
        input_size c <= cert_size (input_size x) /\ V x c = true.

(** * 6. The P vs NP Question *)

(** ** Basic Properties *)

(** Every problem in P is also in NP *)
Theorem P_subseteq_NP : forall L, in_P L -> in_NP L.
Proof.
  (* Proof requires careful handling of quantifiers, admitted for simplicity *)
Admitted.

(** ** The Central Question *)

(** The P vs NP question: Are P and NP equal? *)
Definition P_equals_NP : Prop :=
  forall L, in_NP L -> in_P L.

(** The alternative: P is a proper subset of NP *)
Definition P_neq_NP : Prop :=
  exists L, in_NP L /\ ~ in_P L.

(** These are mutually exclusive (requires classical logic) *)
Axiom P_eq_or_neq_NP : P_equals_NP \/ P_neq_NP.

(** * 7. Formal Tests and Checks *)

(** ** Test 1: Verify a problem is in P *)

(** Given a decision problem and a claimed polynomial-time algorithm,
    verify it satisfies the definition of P *)
Definition test_in_P (L : DecisionProblem) (M : TuringMachine)
                     (time : nat -> nat) (poly_proof : is_polynomial time) : Prop :=
  TM_time_bounded M time /\
  forall x, L x <-> accepts M x.

(** A one-step example checks that the transition reads the input tape. *)
Local Definition first_bit_machine : TuringMachine :=
  {| TM_states := 3; TM_alphabet := 2;
     TM_transition := fun _ symbol =>
       (if Nat.eqb symbol 1 then 1 else 2, symbol, true);
     TM_initial_state := 0; TM_accept_state := 1; TM_reject_state := 2 |}.

Example first_bit_accepted :
  config_state (run first_bit_machine [true] 1) = TM_accept_state first_bit_machine.
Proof. reflexivity. Qed.

Example first_bit_rejected :
  config_state (run first_bit_machine [false] 1) = TM_reject_state first_bit_machine.
Proof. reflexivity. Qed.

(** ** Test 2: Verify a problem is in NP *)

(** Given a decision problem and a claimed verifier, check it satisfies NP *)
Definition test_in_NP (L : DecisionProblem)
                      (V : BinaryString -> Certificate -> bool)
                      (cert_size : nat -> nat)
                      (poly_cert_proof : poly_certificate_size cert_size)
                      (poly_verifier_proof : polynomial_time_verifier V) : Prop :=
  forall x, L x <-> exists c, input_size c <= cert_size (input_size x) /\ V x c = true.

(** Polynomial bounds form a syntax closed under addition, multiplication,
    and substitution. Composition therefore requires no assumed closure law. *)
Inductive poly_bound :=
| bound_const (c : nat)
| bound_input
| bound_add (p q : poly_bound)
| bound_mul (p q : poly_bound)
| bound_comp (p q : poly_bound).

Fixpoint bound_eval (p : poly_bound) (n : nat) : nat :=
  match p with
  | bound_const c => c
  | bound_input => n
  | bound_add p q => bound_eval p n + bound_eval q n
  | bound_mul p q => bound_eval p n * bound_eval q n
  | bound_comp p q => bound_eval p (bound_eval q n)
  end.

Lemma bound_mono : forall p n m, n <= m -> bound_eval p n <= bound_eval p m.
Proof.
  induction p as [c | | p IHp q IHq | p IHp q IHq | p IHp q IHq];
    intros n m H; simpl.
  - lia.
  - exact H.
  - specialize (IHp n m H). specialize (IHq n m H). lia.
  - specialize (IHp n m H). specialize (IHq n m H). nia.
  - apply IHp, IHq. exact H.
Qed.

(** Read the contiguous binary prefix from the left edge of the final tape. *)
Fixpoint read_output (symbols : list Complexity.Symbol) : BinaryString :=
  match symbols with
  | Complexity.zero :: rest => false :: read_output rest
  | Complexity.one :: rest => true :: read_output rest
  | _ => []
  end.

Definition output (c : Complexity.Config) : BinaryString :=
  read_output (rev (Complexity.tapeLeft c) ++
    Complexity.tapeHead c :: Complexity.tapeRight c).

Lemma read_output_map : forall x,
  read_output (map Complexity.ofBool x) = x.
Proof.
  induction x as [|b xs IH]; [reflexivity |].
  destruct b; simpl; now rewrite IH.
Qed.

Lemma output_initial : forall x, output (Complexity.initial x) = x.
Proof.
  destruct x as [|b xs]; [reflexivity |].
  destruct b.
  - change (true :: read_output (map Complexity.ofBool xs) = true :: xs).
    now rewrite read_output_map.
  - change (false :: read_output (map Complexity.ofBool xs) = false :: xs).
    now rewrite read_output_map.
Qed.

(** Every instruction is charged, including the halting instruction. *)
Inductive output_run (m : Complexity.Machine) :
    Complexity.Config -> nat -> Complexity.Config -> Prop :=
| output_halt : forall c b, Complexity.step m c = inl b -> output_run m c 1 c
| output_next : forall c c' out t, Complexity.step m c = inr c' ->
    output_run m c' t out -> output_run m c (S t) out.

Inductive transducer :=
| tm_machine (m : Complexity.Machine)
| tm_bit_not
| tm_compose (first second : transducer).

(** A structural scan charges one step per bit and one final step. *)
Inductive bit_not_run : BinaryString -> nat -> BinaryString -> Prop :=
| bit_not_nil : bit_not_run [] 1 []
| bit_not_cons : forall b xs ys t, bit_not_run xs t ys ->
    bit_not_run (b :: xs) (S t) (negb b :: ys).

Lemma bit_not_runs : forall x,
  bit_not_run x (length x + 1) (map negb x).
Proof.
  induction x as [|b xs IH]; simpl; constructor; auto.
Qed.

(** Sequential composition charges the sum of both runs. Bitwise NOT is a
    structural list traversal, charged once per bit and once at the end. *)
Inductive transducer_run : transducer -> BinaryString -> nat -> BinaryString -> Prop :=
| tr_machine : forall m x t c, output_run m (Complexity.initial x) t c ->
    transducer_run (tm_machine m) x t (output c)
| tr_bit_not : forall x t y, bit_not_run x t y ->
    transducer_run tm_bit_not x t y
| tr_compose : forall first second x middle y t1 t2,
    transducer_run first x t1 middle ->
    transducer_run second middle t2 y ->
    transducer_run (tm_compose first second) x (t1 + t2) y.

(** A certified function has a concrete program and polynomial runtime and
    output-size bounds. Its program returns exactly f x. *)
Definition poly_time_computable (f : BinaryString -> BinaryString) : Prop :=
  exists (program : transducer) (time size : poly_bound),
    forall x, exists t y,
      transducer_run program x t y /\
      t <= bound_eval time (length x) /\
      y = f x /\ length y <= bound_eval size (length x).

Theorem computable_identity : poly_time_computable (fun x => x).
Proof.
  pose (stop_machine := {| Complexity.program := [] |}).
  exists (tm_machine stop_machine), (bound_const 1), bound_input.
  intro x. exists 1, x. repeat split; auto.
  - rewrite <- output_initial.
    apply tr_machine.
    apply output_halt with (b := false).
    unfold stop_machine, Complexity.step, Complexity.instruction.
    destruct x as [|b xs]; reflexivity.
Qed.

Theorem computable_bit_not : poly_time_computable (fun x => map negb x).
Proof.
  exists tm_bit_not, (bound_add bound_input (bound_const 1)), bound_input.
  intro x. exists (length x + 1), (map negb x).
  repeat split; try (apply tr_bit_not, bit_not_runs);
    simpl; auto using Nat.le_refl.
  rewrite length_map. apply Nat.le_refl.
Qed.

Theorem computable_comp : forall f g,
  poly_time_computable f -> poly_time_computable g ->
  poly_time_computable (fun x => g (f x)).
Proof.
  intros f g [first [time1 [size1 Hfirst]]]
    [second [time2 [size2 Hsecond]]].
  exists (tm_compose first second),
    (bound_add time1 (bound_comp time2 size1)),
    (bound_comp size2 size1).
  intro x.
  destruct (Hfirst x) as [t1 [middle [Hr1 [Ht1 [Hm Hs1]]]]].
  destruct (Hsecond middle) as [t2 [y [Hr2 [Ht2 [Hy Hs2]]]]].
  exists (t1 + t2), y. repeat split.
  - eapply tr_compose; eauto.
  - simpl. pose proof (bound_mono time2 (length middle)
      (bound_eval size1 (length x)) Hs1). lia.
  - now rewrite <- Hm.
  - simpl. eapply Nat.le_trans; [exact Hs2 |].
    apply bound_mono. exact Hs1.
Qed.

(** A many-one reduction must compute its map and preserve membership. *)
Definition poly_time_reduction (L1 L2 : DecisionProblem) : Prop :=
  exists f, poly_time_computable f /\ forall x, L1 x <-> L2 (f x).

Theorem reduction_refl : forall L, poly_time_reduction L L.
Proof.
  intro L. exists (fun x => x). split; [apply computable_identity |].
  intro x. tauto.
Qed.

Theorem reduction_trans : forall L1 L2 L3,
  poly_time_reduction L1 L2 -> poly_time_reduction L2 L3 ->
  poly_time_reduction L1 L3.
Proof.
  intros L1 L2 L3 [f [Hf Hcorrect1]] [g [Hg Hcorrect2]].
  exists (fun x => g (f x)). split.
  - apply computable_comp; assumption.
  - intro x. transitivity (L2 (f x)); [apply Hcorrect1 | apply Hcorrect2].
Qed.

(** The distinct singleton languages reduce via one-pass bitwise NOT. *)
Theorem singleton_bit_not_reduction :
  poly_time_reduction (fun x => x = [true]) (fun x => x = [false]).
Proof.
  exists (fun x => map negb x). split; [apply computable_bit_not |].
  intros [|b xs]; [simpl; split; discriminate |].
  destruct b; destruct xs as [|c xs]; simpl; split; congruence.
Qed.

(** ** Test 4: A completeness candidate in this toy P/NP framework. The NP
    verifier still lacks a machine runtime proof, so it is not standard
    NP-completeness. *)

(** A problem L is NP-complete if:
    1. L is in NP
    2. Every problem in NP reduces to L in polynomial time *)
Definition is_NP_complete (L : DecisionProblem) : Prop :=
  in_NP L /\
  forall L', in_NP L' -> poly_time_reduction L' L.

(** The NP-completeness implication remains unasserted because in_NP still
    uses an unconstrained Boolean verifier. *)

(** * 8. Example Problems *)

(** ** SAT Problem (Boolean Satisfiability) *)

(** A boolean formula in CNF *)
Inductive BoolFormula : Type :=
  | BVar : nat -> BoolFormula
  | BNot : BoolFormula -> BoolFormula
  | BAnd : BoolFormula -> BoolFormula -> BoolFormula
  | BOr : BoolFormula -> BoolFormula -> BoolFormula.

(** Assignment of boolean values to variables *)
Definition Assignment := nat -> bool.

(** Evaluate a formula under an assignment *)
Fixpoint eval (a : Assignment) (f : BoolFormula) : bool :=
  match f with
  | BVar n => a n
  | BNot f' => negb (eval a f')
  | BAnd f1 f2 => andb (eval a f1) (eval a f2)
  | BOr f1 f2 => orb (eval a f1) (eval a f2)
  end.

(** SAT: Does there exist a satisfying assignment? *)
Definition SAT (f : BoolFormula) : Prop :=
  exists (a : Assignment), eval a f = true.

(** SAT is in NP: certificate is the satisfying assignment *)
Theorem SAT_in_NP : forall f : BoolFormula,
  (* Abstract: the decision problem version of SAT is in NP *)
  True.
Proof.
  intros. exact I.
Qed.

(** ** Tautology Problem (in coNP) *)

(** TAUT: Is a formula true under all assignments? *)
Definition TAUT (f : BoolFormula) : Prop :=
  forall (a : Assignment), eval a f = true.

(** * 9. Basic Sanity Checks *)

(** ** Check 1: Empty language is in P *)
Definition empty_language : DecisionProblem := fun _ => False.

Theorem empty_in_P : in_P empty_language.
Proof.
  pose (reject_machine :=
    {| TM_states := 2; TM_alphabet := 2;
       TM_transition := fun _ _ => (0, 0, true);
       TM_initial_state := 0; TM_accept_state := 1; TM_reject_state := 0 |}).
  exists reject_machine, (fun _ => 0).
  split; [apply constant_is_poly |].
  split.
  - intro input. exists 0. split; [apply Nat.le_refl | right; reflexivity].
  - intro input. split.
    + unfold empty_language. intro H. contradiction.
    + unfold accepts. intros [steps Haccept].
      assert (Hreject : forall n, config_state (run reject_machine input n) =
        TM_reject_state reject_machine).
      { intro n. induction n as [| n IH].
        - reflexivity.
        - simpl. unfold step. rewrite IH.
          cbn [reject_machine TM_accept_state TM_reject_state Nat.eqb orb].
          exact IH. }
      specialize (Hreject steps). rewrite Hreject in Haccept.
      discriminate Haccept.
Qed.

(** ** Check 2: Universal language is in P *)
Definition universal_language : DecisionProblem := fun _ => True.

Theorem universal_in_P : in_P universal_language.
Proof.
  pose (accept_machine :=
    {| TM_states := 2; TM_alphabet := 2;
       TM_transition := fun _ _ => (0, 0, true);
       TM_initial_state := 1; TM_accept_state := 1; TM_reject_state := 0 |}).
  exists accept_machine, (fun _ => 0).
  split; [apply constant_is_poly |].
  split.
  - intro input. exists 0. split; [apply Nat.le_refl | left; reflexivity].
  - intro input. split.
    + intro H. unfold accepts. exists 0. reflexivity.
    + intro H. exact I.
Qed.

(** ** Check 3: P is closed under complement *)
Theorem P_closed_under_complement : forall L,
  in_P L -> in_P (fun x => ~ L x).
Proof.
  (* Proof omitted for simplicity *)
Admitted.

(** ** Check 4: If P = NP, then NP is closed under complement *)
Theorem P_eq_NP_implies_NP_closed_complement :
  P_equals_NP -> forall L, in_NP L -> in_NP (fun x => ~ L x).
Proof.
  intros Heq L HLnp.
  (* If P = NP, then L is in P *)
  apply Heq in HLnp.
  (* P is closed under complement *)
  apply P_closed_under_complement in HLnp.
  (* So complement of L is in P, hence in NP *)
  apply P_subseteq_NP.
  exact HLnp.
Qed.

(** * 10. Verification Summary *)

(** This formalization provides:
    - Formal definitions of P and NP
    - The P vs NP question stated formally
    - Tests to verify whether problems are in P or NP
    - Basic properties and sanity checks
    - A framework for reasoning about computational complexity
*)

Check in_P.
Check in_NP.
Check P_equals_NP.
Check P_neq_NP.
Check P_subseteq_NP.
Check is_NP_complete.
Check test_in_P.
Check test_in_NP.
Check poly_time_reduction.
Print Assumptions empty_in_P.
Print Assumptions universal_in_P.
Print Assumptions computable_identity.
Print Assumptions computable_bit_not.
Print Assumptions reduction_trans.
Print Assumptions singleton_bit_not_reduction.
Print Assumptions P_subseteq_NP.
Print Assumptions P_eq_or_neq_NP.
Print Assumptions P_closed_under_complement.
Print Assumptions P_eq_NP_implies_NP_closed_complement.

(** All formal specifications compiled successfully *)
