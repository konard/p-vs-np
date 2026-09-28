(** * Issue #532: a shared circuit model and the bridge to the machine model

    Rocq twin of [proofs/experiments/issue532/lean/Circuits.lean]; theorem
    names are aligned.

    Circuit lower bounds in the idea files are stated for the machine-model
    language [SAT] of [Machines.v], over one concrete circuit model: NAND
    straight-line programs.  The model is honest: a circuit is a list of
    gates, its size is the number of gates, and its output is computed by
    [output].

    - [Circuit], [output], [WF]: NAND straight-line programs on [n] input
      wires.
    - [InPPoly], [SuperpolyLowerBound], [not_inPPoly_of_superpoly],
      [superpoly_iff_not_inPPoly]: the class P/poly and a superpolynomial
      circuit lower bound, which are complementary.
    - [PSubsetPPoly]: every language in P has polynomial-size circuits
      (Savage 1972; Pippenger-Fischer 1979; Arora-Barak Theorem 6.6).  It is a
      known theorem that this file does NOT prove; every use is an explicit
      hypothesis named [PSubsetPPoly].
    - [pNotEqualsNP_of_superpoly_sat]: under [SATInNP] (the membership half of
      Cook-Levin, which is NOT proved either, see [Machines.v]) and
      [PSubsetPPoly], a superpolynomial circuit lower bound for SAT gives
      P <> NP.
    - [output_const_true], [output_const_false], [inPPoly_const]: constant
      languages are in P/poly (sanity check of the [0 < n] convention).
    - Shannon counting: [words], [allBool], [fnOfTable],
      [table_of_fnOfTable], [cover_length], [uncovered_table],
      [shannon_codes], [shannon_circuits],
      [four_bit_function_needs_three_gates].
    - [gateBudget], [ShannonAt], [hardAt], [HardLang],
      [shannonAt_two_pow], [exists_superpolyLowerBound],
      [exists_not_inPPoly], [inPPoly_nontrivial]: some language (not claimed
      to be in NP) is outside P/poly, so these notions are not vacuous.
    - [slice], [slice_word]: a language restricted to one input length, as a
      Boolean function of variables [0, ..., n - 1].

    Differences from the Lean file (no axioms are used in this file):
    - [uncovered_table] and [shannon_circuits] have the Lean statements but
      are proved constructively: the uncovered truth table is the first one
      found by [firstUncovered] (a search with decidable list equality),
      not obtained by contradiction.  Helpers [bitsEqb], [firstUncovered],
      [tableOf], [hardTable], [hardTable_spec] and [nodup_append] are new.
    - [hardAt n] is [fnOfTable n (hardTable n (gateBudget n))], a definable
      function, where Lean uses [Classical.choose] under [if ShannonAt n].
      [hardAt_spec] has the same statement.  Consequently
      [exists_superpolyLowerBound], [exists_not_inPPoly] and
      [inPPoly_nontrivial] are axiom-free.  Lean's [exists_not_inPPoly]
      goes through [superpoly_iff_not_inPPoly], whose proof is classical;
      here it uses the constructive [not_inPPoly_of_superpoly].
    - [slice] uses [seq 0 n] for Lean's [List.range n].
    - The forward direction of [superpoly_iff_not_inPPoly] is proved
      constructively as [not_inPPoly_of_superpoly].  The reverse direction
      ([~ InPPoly L -> SuperpolyLowerBound L]) pushes a negation through
      [forall]/[exists] and is not constructively provable in general; Lean
      proves it with [Classical.byContradiction].  Here
      [superpoly_iff_not_inPPoly] takes excluded middle as an explicit
      hypothesis [classic : forall P : Prop, P \/ ~ P] (a premise, not an
      axiom).  The bridge theorems only use the forward direction and are
      axiom-free. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** Gate [(i, j)] appends the NAND of wires [i] and [j]. *)
Definition Circuit := list (nat * nat).

Definition wire (w : list bool) (i : nat) : bool := nth i w false.

(** All wire values: the inputs followed by one wire per gate. *)
Fixpoint wires (w : list bool) (C : Circuit) : list bool :=
  match C with
  | [] => w
  | (i, j) :: C' => wires (w ++ [negb (wire w i && wire w j)]) C'
  end.

(** The output is the last wire ([false] if there are no wires). *)
Definition output (x : Word) (C : Circuit) : bool := last (wires x C) false.

(** Gate [k] only reads the [N] earlier wires. *)
Fixpoint WFfrom (N : nat) (C : Circuit) : Prop :=
  match C with
  | [] => True
  | (i, j) :: C' => i < N /\ j < N /\ WFfrom (N + 1) C'
  end.

(** A well-formed circuit on [n] inputs. *)
Definition WF (n : nat) (C : Circuit) : Prop := WFfrom n C.

(** [C] is a well-formed circuit on [n] inputs that agrees with [L] on every
    word of length [n]. *)
Definition CircuitDecides (n : nat) (C : Circuit) (L : Language) : Prop :=
  WF n C /\ forall x : Word, length x = n -> output x C = L x.

(** The class P/poly: [L] has circuits with polynomially many gates at every
    positive input length.

    Length [0] is excluded on purpose.  A well-formed circuit on [0] inputs
    has no gates ([WF 0 C] forces [C = []]), so its output is the constant
    [false].  If length [0] counted, every language with [L [] = true] (SAT
    among them, since the empty CNF is satisfiable) would be outside P/poly
    for a trivial reason, and [PSubsetPPoly] would be false.  One word per
    length changes no asymptotic notion. *)
Definition InPPoly (L : Language) : Prop :=
  exists p : Polynomial, forall n, 0 < n ->
    exists C : Circuit, length C <= evalPoly p n /\ CircuitDecides n C L.

(** A superpolynomial circuit lower bound: for every polynomial some positive
    input length defeats every circuit of that size (see [InPPoly] for why the
    length is positive). *)
Definition SuperpolyLowerBound (L : Language) : Prop :=
  forall p : Polynomial, exists n, 0 < n /\ forall C : Circuit,
    length C <= evalPoly p n -> WF n C ->
    exists x : Word, length x = n /\ output x C <> L x.

(** The constructive direction of [superpoly_iff_not_inPPoly]. *)
Theorem not_inPPoly_of_superpoly : forall L, SuperpolyLowerBound L -> ~ InPPoly L.
Proof.
  intros L h [p hp].
  destruct (h p) as [n [hn0 hn]].
  destruct (hp n hn0) as [C [hl [hw hc]]].
  destruct (hn C hl hw) as [x [hx hne]].
  exact (hne (hc x hx)).
Qed.

(** Lean proves the reverse direction classically; here excluded middle is an
    explicit hypothesis [classic] (not an axiom). *)
Theorem superpoly_iff_not_inPPoly : (forall P : Prop, P \/ ~ P) ->
  forall L, SuperpolyLowerBound L <-> ~ InPPoly L.
Proof.
  intros classic L. split; [apply not_inPPoly_of_superpoly |].
  intros h p.
  destruct (classic (exists n, 0 < n /\ forall C : Circuit,
    length C <= evalPoly p n -> WF n C ->
    exists x : Word, length x = n /\ output x C <> L x)) as [hyes | hno];
    [exact hyes |].
  exfalso. apply h. exists p. intros n hn0.
  destruct (classic (exists C : Circuit, length C <= evalPoly p n /\
    CircuitDecides n C L)) as [hC | hC]; [exact hC |].
  exfalso. apply hno. exists n. split; [exact hn0 |]. intros C hl hw.
  destruct (classic (exists x : Word, length x = n /\ output x C <> L x))
    as [hx | hx]; [exact hx |].
  exfalso. apply hC. exists C. split; [exact hl | split; [exact hw |]].
  intros x hlen. destruct (Bool.bool_dec (output x C) (L x)) as [e | ne];
    [exact e |].
  exfalso. exact (hx (ex_intro _ x (conj hlen ne))).
Qed.

(** Known theorem, not mechanised here.  Every language decided by a
    polynomial-time [Machine] has polynomial-size NAND circuits (Savage 1972;
    Pippenger-Fischer 1979; Arora-Barak Theorem 6.6).  The missing part is
    the tableau construction for this machine model. *)
Definition PSubsetPPoly : Prop := forall L : Language, InP L -> InPPoly L.

(** A language outside P/poly is outside P, given [PSubsetPPoly]. *)
Theorem not_inP_of_not_inPPoly : PSubsetPPoly -> forall L : Language,
  ~ InPPoly L -> ~ InP L.
Proof. intros hP L h hL. exact (h (hP L hL)). Qed.

(** Bridge.  A superpolynomial circuit lower bound for SAT gives P <> NP,
    using the membership half of Cook-Levin and [PSubsetPPoly]. *)
Theorem pNotEqualsNP_of_superpoly_sat : SATInNP -> PSubsetPPoly ->
  SuperpolyLowerBound SAT -> PNotEqualsNP.
Proof.
  intros mem hP h hEq.
  exact (not_inP_of_not_inPPoly hP SAT (not_inPPoly_of_superpoly SAT h)
    (inP_sat_of_pEqualsNP mem hEq)).
Qed.

(** The same bridge for any NP language. *)
Theorem pNotEqualsNP_of_superpoly : PSubsetPPoly -> forall L : Language,
  InNP L -> SuperpolyLowerBound L -> PNotEqualsNP.
Proof.
  intros hP L mem h hEq.
  exact (not_inP_of_not_inPPoly hP L (not_inPPoly_of_superpoly L h) (hEq L mem)).
Qed.

(** ** Sanity check: constant languages are in P/poly

    With the positive-length convention every constant language has two- or
    three-gate circuits, so [PSubsetPPoly] is not refuted by a degenerate
    case. *)

Theorem wire_append_self : forall (x : list bool) (b : bool),
  wire (x ++ [b]) (length x) = b.
Proof. intros x b. unfold wire. apply nth_middle. Qed.

Theorem wire_append_lt : forall (x : list bool) (b : bool) (i : nat),
  i < length x -> wire (x ++ [b]) i = wire x i.
Proof. intros x b i h. unfold wire. apply app_nth1. exact h. Qed.

(** The circuit [[(0,0); (0,n)]] outputs [true] on every input of positive
    length. *)
Theorem output_const_true : forall x : Word, 0 < length x ->
  output x [(0, 0); (0, length x)] = true.
Proof.
  intros x hx. unfold output. cbn [wires]. rewrite last_last.
  rewrite wire_append_self, wire_append_lt by exact hx.
  destruct (wire x 0); reflexivity.
Qed.

(** The circuit [[(0,0); (0,n); (n+1,n+1)]] outputs [false] on every input of
    positive length. *)
Theorem output_const_false : forall x : Word, 0 < length x ->
  output x [(0, 0); (0, length x); (length x + 1, length x + 1)] = false.
Proof.
  intros x hx. unfold output. cbn [wires]. rewrite last_last.
  set (a := negb (wire x 0 && wire x 0)).
  assert (e : length x + 1 = length (x ++ [a])) by (rewrite length_app; reflexivity).
  rewrite e, wire_append_self.
  rewrite wire_append_self, wire_append_lt by exact hx.
  unfold a. destruct (wire x 0); reflexivity.
Qed.

(** Every constant language is in P/poly. *)
Theorem inPPoly_const : forall b : bool, InPPoly (fun _ => b).
Proof.
  intro b. exists {| coefficient := 3; degree := 0 |}. intros n hn.
  destruct b.
  - exists [(0, 0); (0, n)].
    split; [unfold evalPoly; simpl; lia |].
    split; [unfold WF; simpl; repeat split; lia |].
    intros x hx. subst n. apply output_const_true. exact hn.
  - exists [(0, 0); (0, n); (n + 1, n + 1)].
    split; [unfold evalPoly; simpl; lia |].
    split; [unfold WF; simpl; repeat split; lia |].
    intros x hx. subst n. apply output_const_false. exact hn.
Qed.

(** * Shannon counting over the shared circuit model

    Moved from Idea 30 (in Lean) and stated over the shared [wires],
    [output] and [WF].  Lists of length [s] over an alphabet of size [m] are
    exactly [m ^ s]; truth tables on [n] bits are exactly [2 ^ (2 ^ n)] and
    duplicate-free; a list of codes shorter than a duplicate-free list cannot
    cover it.  Hence, if [(g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n)],
    some Boolean function on [n] bits has no circuit with at most [g] gates
    ([shannon_circuits]).

    Unlike Lean, every step here is constructive: the uncovered truth table is
    found by a search ([firstUncovered]) over decidable list equality. *)

(** ** Words over a finite alphabet *)

(** Prefix every word of [W] with every letter of the alphabet. *)
Fixpoint consAll {A : Type} (l : list A) (W : list (list A)) : list (list A) :=
  match l with
  | [] => []
  | a :: l' => map (fun w => a :: w) W ++ consAll l' W
  end.

(** All words of length [s] over [alph]. *)
Fixpoint words {A : Type} (alph : list A) (s : nat) : list (list A) :=
  match s with
  | 0 => [[]]
  | S s' => consAll alph (words alph s')
  end.

Theorem consAll_length : forall {A : Type} (l : list A) (W : list (list A)),
  length (consAll l W) = length l * length W.
Proof.
  intros A l W. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite length_app, length_map, IH. reflexivity.
Qed.

(** There are exactly [m ^ s] words of length [s] over an alphabet of size
    [m]. *)
Theorem words_length : forall {A : Type} (alph : list A) (s : nat),
  length (words alph s) = length alph ^ s.
Proof.
  intros A alph s. induction s as [| s IH]; simpl; [reflexivity |].
  rewrite consAll_length, IH. reflexivity.
Qed.

Theorem mem_consAll : forall {A : Type} (l : list A) (W : list (list A)) (w : list A),
  In w (consAll l W) <-> exists a, In a l /\ exists v, In v W /\ w = a :: v.
Proof.
  intros A l W w. induction l as [| b l IH]; simpl.
  - split; [contradiction | intros [a [[] _]]].
  - rewrite in_app_iff, in_map_iff, IH. split.
    + intros [[v [e hv]] | [a [ha [v [hv e]]]]].
      * exists b. split; [left; reflexivity |]. exists v. auto.
      * exists a. split; [right; exact ha |]. exists v. auto.
    + intros [a [[hab | ha] [v [hv e]]]].
      * subst a. left. exists v. auto.
      * right. exists a. split; [exact ha |]. exists v. auto.
Qed.

(** [words alph s] contains exactly the words of length [s] over [alph]
    (soundness and completeness). *)
Theorem mem_words : forall {A : Type} (alph : list A) (s : nat) (w : list A),
  In w (words alph s) <-> length w = s /\ forall a, In a w -> In a alph.
Proof.
  intros A alph s. induction s as [| s IH]; intro w.
  - simpl. destruct w as [| a w]; split.
    + intros _. split; [reflexivity | intros a []].
    + intros _. left. reflexivity.
    + intros [h | []]. discriminate.
    + intros [h _]. discriminate.
  - simpl. rewrite mem_consAll. split.
    + intros [a [ha [v [hv e]]]]. subst w. apply IH in hv. destruct hv as [hl hall].
      split; [simpl; rewrite hl; reflexivity |].
      intros b [hb | hb]; [subst b; exact ha | exact (hall b hb)].
    + intros [hl hall]. destruct w as [| a v]; [discriminate |].
      exists a. split; [apply hall; left; reflexivity |].
      exists v. split; [| reflexivity].
      apply IH. split; [simpl in hl; lia |].
      intros b hb. apply hall. right. exact hb.
Qed.

Theorem nodup_map_cons : forall {A : Type} (a : A) (W : list (list A)),
  NoDup W -> NoDup (map (fun w => a :: w) W).
Proof.
  intros A a W h. induction h as [| v W hv hW IH]; simpl; constructor; [| exact IH].
  intro hin. apply in_map_iff in hin. destruct hin as [u [e hu]].
  injection e as e. subst u. exact (hv hu).
Qed.

(** Concatenation of duplicate-free lists with disjoint members (proved here
    so as not to depend on the stdlib version). *)
Lemma nodup_append : forall {A : Type} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 h1. induction h1 as [| x l1 hx h1 IH]; intros h2 hdis; simpl;
    [exact h2 |].
  constructor.
  - rewrite in_app_iff. intros [hin | hin]; [exact (hx hin) |].
    exact (hdis x (or_introl eq_refl) hin).
  - apply IH; [exact h2 |]. intros a ha. apply hdis. right. exact ha.
Qed.

Theorem consAll_nodup : forall {A : Type} (l : list A) (W : list (list A)),
  NoDup l -> NoDup W -> NoDup (consAll l W).
Proof.
  intros A l W hl hW. induction hl as [| a l ha hl IH]; simpl; [constructor |].
  apply nodup_append; [apply nodup_map_cons; exact hW | exact IH |].
  intros x hx hy. apply in_map_iff in hx. destruct hx as [v [ev _]].
  apply mem_consAll in hy. destruct hy as [b [hb [u [_ eu]]]].
  subst x. injection eu as eab _. subst b. exact (ha hb).
Qed.

(** Words over a duplicate-free alphabet are duplicate-free. *)
Theorem words_nodup : forall {A : Type} (alph : list A), NoDup alph ->
  forall s, NoDup (words alph s).
Proof.
  intros A alph h s. induction s as [| s IH]; simpl.
  - constructor; [intros [] | constructor].
  - apply consAll_nodup; assumption.
Qed.

(** ** Truth tables *)

(** All Boolean inputs of length [n]. *)
Definition allBool (n : nat) : list (list bool) := words [false; true] n.

Theorem allBool_length : forall n, length (allBool n) = 2 ^ n.
Proof. intro n. apply words_length. Qed.

Theorem allBool_nodup : forall n, NoDup (allBool n).
Proof.
  intro n. apply words_nodup. constructor.
  - intros [h | []]. discriminate.
  - constructor; [intros [] | constructor].
Qed.

Theorem mem_allBool : forall n (x : list bool), In x (allBool n) <-> length x = n.
Proof.
  intros n x. unfold allBool. rewrite mem_words. split.
  - intros [h _]. exact h.
  - intro h. split; [exact h |]. intros [] _; simpl; auto.
Qed.

(** Truth tables of [n]-bit functions: exactly [2 ^ (2 ^ n)] of them. *)
Theorem tables_length : forall n, length (allBool (2 ^ n)) = 2 ^ (2 ^ n).
Proof. intro n. apply allBool_length. Qed.

(** The function whose truth table (in the order of [allBool n]) is [tt]. *)
Fixpoint fnOfTable (n : nat) (tt : list bool) (x : list bool) : bool :=
  match n with
  | 0 => hd false tt
  | S n' =>
      match x with
      | [] => false
      | b :: x' => fnOfTable n' (if b then skipn (2 ^ n') tt else firstn (2 ^ n') tt) x'
      end
  end.

Theorem allBool_succ : forall n,
  allBool (S n) = map (fun w => false :: w) (allBool n) ++
                  map (fun w => true :: w) (allBool n).
Proof. intro n. unfold allBool. simpl. rewrite app_nil_r. reflexivity. Qed.

(** Every table of length [2 ^ n] is the truth table of a function. *)
Theorem table_of_fnOfTable : forall n (tt : list bool), length tt = 2 ^ n ->
  map (fnOfTable n tt) (allBool n) = tt.
Proof.
  intro n. induction n as [| n IH]; intros tt h.
  - destruct tt as [| b [| c tt]]; simpl in h; try discriminate. reflexivity.
  - rewrite allBool_succ, map_app, !map_map. simpl.
    assert (hpow : 2 ^ S n = 2 ^ n + 2 ^ n) by (simpl; lia).
    rewrite hpow in h.
    change (map (fnOfTable n (firstn (2 ^ n) tt)) (allBool n) ++
            map (fnOfTable n (skipn (2 ^ n) tt)) (allBool n) = tt).
    rewrite (IH (firstn (2 ^ n) tt)) by (rewrite length_firstn; lia).
    rewrite (IH (skipn (2 ^ n) tt)) by (rewrite length_skipn; lia).
    apply firstn_skipn.
Qed.

(** ** Pigeonhole *)

(** A duplicate-free list covered by the image of [codes] is no longer than
    [codes]. *)
Theorem cover_length : forall {Code : Type} (decode : Code -> list bool)
    (targets : list (list bool)) (codes : list Code),
  NoDup targets -> (forall t, In t targets -> exists c, In c codes /\ decode c = t) ->
  length targets <= length codes.
Proof.
  intros Code decode targets codes hnd hcov.
  rewrite <- (length_map decode codes). apply NoDup_incl_length; [exact hnd |].
  intros t ht. destruct (hcov t ht) as [c [hc e]]. apply in_map_iff. exists c. auto.
Qed.

(** Decidable equality of bit strings, as a Boolean. *)
Definition bitsEqb (u v : list bool) : bool :=
  if list_eq_dec Bool.bool_dec u v then true else false.

Theorem bitsEqb_true : forall u v, bitsEqb u v = true <-> u = v.
Proof.
  intros u v. unfold bitsEqb. destruct (list_eq_dec Bool.bool_dec u v) as [e | ne].
  - split; intros _; [exact e | reflexivity].
  - split; intro h; [discriminate | contradiction].
Qed.

(** The first target (in list order) that no code describes. *)
Definition firstUncovered {Code : Type} (decode : Code -> list bool) (codes : list Code)
    (targets : list (list bool)) : option (list bool) :=
  find (fun t => negb (existsb (fun c => bitsEqb (decode c) t) codes)) targets.

Theorem firstUncovered_some : forall {Code : Type} (decode : Code -> list bool) codes
    targets t, firstUncovered decode codes targets = Some t ->
  In t targets /\ forall c, In c codes -> decode c <> t.
Proof.
  intros Code decode codes targets t h. apply find_some in h. destruct h as [ht hf].
  split; [exact ht |]. intros c hc e.
  assert (hex : existsb (fun c => bitsEqb (decode c) t) codes = true).
  { apply existsb_exists. exists c. split; [exact hc | apply bitsEqb_true; exact e]. }
  rewrite hex in hf. discriminate.
Qed.

Theorem firstUncovered_none : forall {Code : Type} (decode : Code -> list bool) codes
    targets, firstUncovered decode codes targets = None ->
  forall t, In t targets -> exists c, In c codes /\ decode c = t.
Proof.
  intros Code decode codes targets h t ht.
  pose proof (find_none _ _ h t ht) as hf. simpl in hf.
  apply negb_false_iff, existsb_exists in hf. destruct hf as [c [hc e]].
  exists c. split; [exact hc | apply bitsEqb_true; exact e].
Qed.

(** Abstract Shannon counting: fewer codes than truth tables leaves a table
    uncovered.  (Lean argues by contradiction; here the table is found by
    [firstUncovered].) *)
Theorem uncovered_table : forall {Code : Type} (decode : Code -> list bool) (n : nat)
    (codes : list Code), length codes < 2 ^ (2 ^ n) ->
  exists t, In t (allBool (2 ^ n)) /\ forall c, In c codes -> decode c <> t.
Proof.
  intros Code decode n codes h.
  destruct (firstUncovered decode codes (allBool (2 ^ n))) as [t |] eqn:E.
  - exists t. exact (firstUncovered_some _ _ _ _ E).
  - exfalso. pose proof (cover_length decode _ codes (allBool_nodup _)
      (firstUncovered_none _ _ _ E)) as hl.
    rewrite tables_length in hl. lia.
Qed.

(** Codes of length at most [s] over an alphabet, as one list. *)
Fixpoint codesUpTo {A : Type} (alph : list A) (s : nat) : list (list A) :=
  match s with
  | 0 => words alph 0
  | S s' => codesUpTo alph s' ++ words alph (S s')
  end.

Theorem codesUpTo_length : forall {A : Type} (alph : list A), 1 <= length alph ->
  forall s, length (codesUpTo alph s) <= (s + 1) * length alph ^ s.
Proof.
  intros A alph h s. induction s as [| s IH]; [simpl; lia |].
  cbn [codesUpTo]. rewrite length_app, words_length.
  assert (hp : length alph ^ s <= length alph ^ S s)
    by (apply Nat.pow_le_mono_r; lia).
  assert (hm : (s + 1) * length alph ^ s <= (s + 1) * length alph ^ S s)
    by (apply Nat.mul_le_mono_l; exact hp).
  generalize dependent (length alph ^ S s). intros P hp hm.
  generalize dependent (length alph ^ s). intros Q IH hp hm. nia.
Qed.

Theorem mem_codesUpTo : forall {A : Type} (alph : list A) (s : nat) (w : list A),
  length w <= s -> (forall a, In a w -> In a alph) -> In w (codesUpTo alph s).
Proof.
  intros A alph s w hl ha. induction s as [| s IH].
  - change (In w (words alph 0)). apply mem_words. split; [lia | exact ha].
  - cbn [codesUpTo]. apply in_app_iff.
    destruct (le_lt_dec (length w) s) as [hs | hs].
    + left. exact (IH hs).
    + right. apply mem_words. split; [lia | exact ha].
Qed.

(** Shannon counting for any code-based description of functions: if there
    are fewer codes of length at most [s] (over an alphabet of size at least
    [1]) than functions on [n] bits, some table is not described by any such
    code. *)
Theorem shannon_codes : forall {A : Type} (alph : list A), 1 <= length alph ->
  forall (decode : list A -> list bool) (n s : nat),
  (s + 1) * length alph ^ s < 2 ^ (2 ^ n) ->
  exists t, In t (allBool (2 ^ n)) /\ forall w, length w <= s ->
    (forall a, In a w -> In a alph) -> decode w <> t.
Proof.
  intros A alph h1 decode n s h.
  destruct (uncovered_table decode n (codesUpTo alph s)
    (Nat.le_lt_trans _ _ _ (codesUpTo_length alph h1 s) h)) as [t [ht hno]].
  exists t. split; [exact ht |]. intros w hl ha. exact (hno w (mem_codesUpTo alph s w hl ha)).
Qed.

(** ** Circuits as codes *)

(** All pairs from two lists. *)
Fixpoint pairsOf (l m : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | a :: l' => map (fun b => (a, b)) m ++ pairsOf l' m
  end.

Theorem pairsOf_length : forall l m, length (pairsOf l m) = length l * length m.
Proof.
  intros l m. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite length_app, length_map, IH. reflexivity.
Qed.

Theorem mem_pairsOf : forall l m a b, In a l -> In b m -> In (a, b) (pairsOf l m).
Proof.
  intros l m a b ha hb. induction l as [| c l IH]; [destruct ha |].
  simpl. apply in_app_iff. destruct ha as [e | ha].
  - subst c. left. apply in_map_iff. exists b. auto.
  - right. exact (IH ha).
Qed.

Theorem wf_bound : forall N (C : Circuit), WFfrom N C ->
  forall p, In p C -> fst p < N + length C /\ snd p < N + length C.
Proof.
  intros N C. revert N. induction C as [| [i j] C IH]; intros N h p hp;
    [destruct hp |].
  destruct h as [hi [hj hC]]. simpl length.
  destruct hp as [e | hp].
  - subst p. simpl. lia.
  - destruct (IH (N + 1) hC p hp). lia.
Qed.

(** The gate alphabet for circuits with at most [g] gates on [n] inputs. *)
Definition gateAlphabet (n g : nat) : list (nat * nat) :=
  pairsOf (seq 0 (n + g)) (seq 0 (n + g)).

Theorem gateAlphabet_length : forall n g,
  length (gateAlphabet n g) = (n + g) * (n + g).
Proof. intros n g. unfold gateAlphabet. rewrite pairsOf_length, length_seq. reflexivity. Qed.

Theorem wf_in_alphabet : forall n g (C : Circuit), WF n C -> length C <= g ->
  forall p, In p C -> In p (gateAlphabet n g).
Proof.
  intros n g C hw hl [i j] hp.
  destruct (wf_bound n C hw (i, j) hp) as [hi hj]. simpl in hi, hj.
  apply mem_pairsOf; apply in_seq; lia.
Qed.

(** The truth table of a circuit on [n] inputs, in the order of
    [allBool n]. *)
Definition tableOf (n : nat) (C : Circuit) : list bool :=
  map (fun x => output x C) (allBool n).

(** A table on [n] bits that no circuit with at most [g] gates computes, when
    the Shannon inequality holds: the first such table in the order of
    [allBool (2 ^ n)] (the empty list, a dummy, if there is none). *)
Definition hardTable (n g : nat) : list bool :=
  match firstUncovered (tableOf n) (codesUpTo (gateAlphabet n g) g) (allBool (2 ^ n)) with
  | Some t => t
  | None => []
  end.

(** [fnOfTable n (hardTable n g)] is computed by no well-formed circuit with
    at most [g] gates. *)
Theorem hardTable_spec : forall n g,
  (g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n) ->
  forall C, WF n C -> length C <= g ->
    exists x, length x = n /\ output x C <> fnOfTable n (hardTable n g) x.
Proof.
  intros n g h C hw hl.
  unfold hardTable.
  destruct (firstUncovered (tableOf n) (codesUpTo (gateAlphabet n g) g)
    (allBool (2 ^ n))) as [t |] eqn:E.
  - destruct (firstUncovered_some _ _ _ _ E) as [ht hno].
    assert (htl : length t = 2 ^ n) by (apply mem_allBool; exact ht).
    destruct (find (fun x => negb (Bool.eqb (output x C) (fnOfTable n t x))) (allBool n))
      as [x |] eqn:F.
    + apply find_some in F. destruct F as [hx hne].
      exists x. split; [apply mem_allBool; exact hx |].
      intro e. rewrite e, Bool.eqb_reflx in hne. discriminate.
    + exfalso. apply (hno C).
      * apply mem_codesUpTo; [exact hl |]. exact (wf_in_alphabet n g C hw hl).
      * rewrite <- (table_of_fnOfTable n t htl). unfold tableOf.
        apply map_ext_in. intros x hx. pose proof (find_none _ _ F x hx) as hf.
        simpl in hf. apply negb_false_iff, Bool.eqb_prop in hf. exact hf.
  - exfalso.
    pose proof (cover_length (tableOf n) _ _ (allBool_nodup _)
      (firstUncovered_none _ _ _ E)) as hc.
    rewrite tables_length in hc.
    destruct (Nat.eq_dec (n + g) 0) as [h0 | h0].
    + assert (n = 0) by lia. assert (g = 0) by lia. subst n g.
      simpl in hc. lia.
    + pose proof (codesUpTo_length (gateAlphabet n g)
        ltac:(rewrite gateAlphabet_length; nia) g) as hb.
      rewrite gateAlphabet_length in hb.
      exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ (Nat.le_trans _ _ _ hc hb) h)).
Qed.

(** Shannon's counting theorem for NAND circuits: if
    [(g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n)], some Boolean function
    on [n] bits is computed by no well-formed circuit with at most [g]
    gates. *)
Theorem shannon_circuits : forall n g,
  (g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n) ->
  exists f : list bool -> bool, forall C, WF n C -> length C <= g ->
    exists x, length x = n /\ output x C <> f x.
Proof.
  intros n g h. exists (fnOfTable n (hardTable n g)). exact (hardTable_spec n g h).
Qed.

(** Concrete instance: some Boolean function on 4 bits needs more than 2 NAND
    gates. *)
Theorem four_bit_function_needs_three_gates :
  exists f : list bool -> bool, forall C, WF 4 C -> length C <= 2 ->
    exists x, length x = 4 /\ output x C <> f x.
Proof. apply shannon_circuits. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

(** ** A language outside P/poly

    Counting is non-explicit.  The language [HardLang] below takes, at every
    length [n = 2 ^ a], a function that no circuit with [2 ^ (a * a)] gates
    computes.  In Lean it is chosen with [Classical.choose]; here it is the
    first uncovered truth table ([hardTable]), so [HardLang] is a definable
    (if astronomically slow) Boolean function and no choice is used.  It is
    not known to lie in NP.  Its role is non-vacuity: [~ InPPoly L] and
    [SuperpolyLowerBound L] are satisfiable. *)

(** The gate budget at length [n]: [2 ^ (log2 n)^2], superpolynomial in
    [n]. *)
Definition gateBudget (n : nat) : nat := 2 ^ (Nat.log2 n * Nat.log2 n).

(** The Shannon inequality for [n] inputs and budget [gateBudget n]. *)
Definition ShannonAt (n : nat) : Prop :=
  (gateBudget n + 1) * ((n + gateBudget n) * (n + gateBudget n)) ^ gateBudget n <
    2 ^ (2 ^ n).

(** A function on [n] bits with no circuit of [gateBudget n] gates when the
    Shannon inequality holds.  (Lean returns the constant [false] when it
    fails; here no case split is needed, [hardAt_spec] is the same.) *)
Definition hardAt (n : nat) : Language := fnOfTable n (hardTable n (gateBudget n)).

Theorem hardAt_spec : forall n, ShannonAt n ->
  forall C, WF n C -> length C <= gateBudget n ->
    exists x, length x = n /\ output x C <> hardAt n x.
Proof. intros n h. exact (hardTable_spec n (gateBudget n) h). Qed.

(** The hard language: at length [n] it agrees with [hardAt n]. *)
Definition HardLang : Language := fun x => hardAt (length x) x.

Theorem sq_step : forall m, 7 <= m -> 2 * (m * m) + 2 < 2 ^ m ->
  2 * ((m + 1) * (m + 1)) + 2 < 2 ^ (m + 1).
Proof.
  intros m hm ih. rewrite Nat.add_1_r, Nat.pow_succ_r'.
  assert (hmm : 2 * m <= m * m) by (apply Nat.mul_le_mono_r; lia).
  nia.
Qed.

Theorem two_mul_sq_lt_two_pow : forall a, 7 <= a -> 2 * (a * a) + 2 < 2 ^ a.
Proof.
  intro a. induction a as [| a IH]; intro ha; [lia |].
  destruct (Nat.eq_dec a 6) as [e | hne].
  - subst a. apply Nat.ltb_lt. reflexivity.
  - replace (S a) with (a + 1) by lia. apply sq_step; [lia | apply IH; lia].
Qed.

Theorem le_two_pow_self : forall a, a + 1 <= 2 ^ a.
Proof. intro a. induction a as [| a IH]; simpl; lia. Qed.

(** The Shannon inequality holds at every length [2 ^ a] with [a >= 7]. *)
Theorem shannonAt_two_pow : forall a, 7 <= a -> ShannonAt (2 ^ a).
Proof.
  intros a ha. unfold ShannonAt, gateBudget.
  rewrite Nat.log2_pow2 by lia.
  remember (a * a) as B eqn:hB.
  assert (haB : a <= B) by (subst B; nia).
  assert (hkey : 2 * B + 2 < 2 ^ a) by (subst B; apply two_mul_sq_lt_two_pow; exact ha).
  assert (hn : 2 ^ a <= 2 ^ B) by (apply Nat.pow_le_mono_r; lia).
  assert (hsum : 2 ^ a + 2 ^ B <= 2 ^ (B + 1))
    by (rewrite Nat.add_1_r, Nat.pow_succ_r'; lia).
  assert (hsq : (2 ^ a + 2 ^ B) * (2 ^ a + 2 ^ B) <= 2 ^ (2 * B + 2)).
  { replace (2 * B + 2) with ((B + 1) + (B + 1)) by lia.
    rewrite Nat.pow_add_r. apply Nat.mul_le_mono; exact hsum. }
  assert (hpow : ((2 ^ a + 2 ^ B) * (2 ^ a + 2 ^ B)) ^ 2 ^ B <=
                 2 ^ ((2 * B + 2) * 2 ^ B)).
  { rewrite Nat.pow_mul_r. apply Nat.pow_le_mono_l. exact hsq. }
  assert (hg1 : 2 ^ B + 1 <= 2 ^ (2 ^ B)) by apply le_two_pow_self.
  assert (htot : (2 ^ B + 1) * ((2 ^ a + 2 ^ B) * (2 ^ a + 2 ^ B)) ^ 2 ^ B <=
                 2 ^ ((2 * B + 3) * 2 ^ B)).
  { replace ((2 * B + 3) * 2 ^ B) with (2 ^ B + (2 * B + 2) * 2 ^ B) by lia.
    rewrite Nat.pow_add_r. apply Nat.mul_le_mono; assumption. }
  assert (hexp : (2 * B + 3) * 2 ^ B < 2 ^ (2 ^ a)).
  { assert (h1 : 2 * B + 3 <= 2 ^ (B + 2)).
    { pose proof (le_two_pow_self B).
      rewrite Nat.pow_add_r. simpl (2 ^ 2). lia. }
    assert (h2 : (2 * B + 3) * 2 ^ B <= 2 ^ (2 * B + 2)).
    { replace (2 * B + 2) with ((B + 2) + B) by lia.
      rewrite Nat.pow_add_r. apply Nat.mul_le_mono_r. exact h1. }
    eapply Nat.le_lt_trans; [exact h2 |].
    apply Nat.pow_lt_mono_r; [lia | exact hkey]. }
  eapply Nat.le_lt_trans; [exact htot |].
  apply Nat.pow_lt_mono_r; [lia | exact hexp].
Qed.

(** A polynomial is below the gate budget at length [2 ^ a] once [a] is
    large. *)
Theorem poly_le_gateBudget : forall (p : Polynomial) a,
  coefficient p + degree p + 1 <= a -> evalPoly p (2 ^ a) <= gateBudget (2 ^ a).
Proof.
  intros [c k] a ha. unfold gateBudget, evalPoly. simpl in ha |- *.
  rewrite Nat.log2_pow2 by lia.
  assert (h1 : 2 ^ a + 1 <= 2 ^ (a + 1)).
  { replace (a + 1) with (S a) by lia. rewrite Nat.pow_succ_r'.
    pose proof (Nat.pow_nonzero 2 a ltac:(lia)). lia. }
  assert (h2 : (2 ^ a + 1) ^ k <= 2 ^ ((a + 1) * k)).
  { rewrite Nat.pow_mul_r. apply Nat.pow_le_mono_l. exact h1. }
  assert (hc : c <= 2 ^ c) by (pose proof (le_two_pow_self c); lia).
  assert (h3 : c * (2 ^ a + 1) ^ k <= 2 ^ (c + (a + 1) * k)).
  { rewrite Nat.pow_add_r. apply Nat.mul_le_mono; assumption. }
  eapply Nat.le_trans; [exact h3 |]. apply Nat.pow_le_mono_r; [lia |].
  assert (h4 : c <= a * c) by nia.
  assert (h5 : a * (c + k + 1) <= a * a) by (apply Nat.mul_le_mono_l; lia).
  nia.
Qed.

(** Non-vacuity of circuit lower bounds.  Some language has a
    superpolynomial circuit lower bound.  The witness [HardLang] comes from
    Shannon counting and is not claimed to be in NP. *)
Theorem exists_superpolyLowerBound : exists L : Language, SuperpolyLowerBound L.
Proof.
  exists HardLang. intro p.
  set (a := coefficient p + degree p + 8).
  exists (2 ^ a). split; [pose proof (Nat.pow_nonzero 2 a ltac:(lia)); lia |].
  intros C hl hw.
  pose proof (shannonAt_two_pow a ltac:(unfold a; lia)) as hsh.
  pose proof (poly_le_gateBudget p a ltac:(unfold a; lia)) as hle.
  destruct (hardAt_spec (2 ^ a) hsh C hw (Nat.le_trans _ _ _ hl hle)) as [x [hx hne]].
  exists x. split; [exact hx |]. unfold HardLang. rewrite hx. exact hne.
Qed.

(** Non-vacuity of [~ InPPoly].  Some language is outside P/poly. *)
Theorem exists_not_inPPoly : exists L : Language, ~ InPPoly L.
Proof.
  destruct exists_superpolyLowerBound as [L hL].
  exists L. exact (not_inPPoly_of_superpoly L hL).
Qed.

(** [InPPoly] is not the trivial class: it contains every constant language
    and misses [HardLang]. *)
Theorem inPPoly_nontrivial : (exists L, InPPoly L) /\ (exists L, ~ InPPoly L).
Proof.
  split; [exists (fun _ => true); apply inPPoly_const | exact exists_not_inPPoly].
Qed.

(** ** Slices: from a language to finite Boolean functions

    Formula models in the idea files evaluate under an assignment
    [nat -> bool].  [slice L n] is the Boolean function on variables
    [0, ..., n - 1] that [L] computes at input length [n].  It ties a formula
    family to a language. *)

(** [L] restricted to inputs of length [n], read from variables
    [0, ..., n - 1]. *)
Definition slice (L : Language) (n : nat) (rho : nat -> bool) : bool :=
  L (map rho (seq 0 n)).

Lemma map_nth_seq_self : forall (x : list bool) start,
  map (fun i => nth (i - start) x false) (seq start (length x)) = x.
Proof.
  intro x. induction x as [| b x IH]; intro start; simpl; [reflexivity |].
  rewrite Nat.sub_diag. f_equal.
  transitivity (map (fun i => nth (i - S start) x false) (seq (S start) (length x)));
    [| apply IH].
  apply map_ext_in. intros i hi.
  apply in_seq in hi. replace (i - start) with (S (i - S start)) by lia. reflexivity.
Qed.

(** [slice L n] evaluated on the bits of a word of length [n] is [L] of that
    word. *)
Theorem slice_word : forall (L : Language) (x : Word),
  slice L (length x) (fun i => nth i x false) = L x.
Proof.
  intros L x. unfold slice. f_equal.
  transitivity (map (fun i => nth (i - 0) x false) (seq 0 (length x)));
    [| apply map_nth_seq_self].
  apply map_ext_in. intros i _. rewrite Nat.sub_0_r. reflexivity.
Qed.
