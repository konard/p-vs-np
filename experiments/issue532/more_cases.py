"""General proof obligations and countermodels for the second issue #532 batch.

Each tuple contains a slug, a standalone Lean body, and a standalone Rocq body.
The paired statements are intentionally small: they isolate a valid inference
or refute an invalid one; none claims a complexity-class separation.
"""

MORE_CASES = [
    (
        "21_branching_exhaustive",
        r"""theorem tested (P Q : Prop) :
    (P ∨ Q) ↔ ∃ b : Bool, if b then P else Q := by
  constructor
  · intro h
    rcases h with hp | hq
    · exact ⟨true, hp⟩
    · exact ⟨false, hq⟩
  · rintro ⟨b, h⟩
    cases b with
    | false => exact Or.inr h
    | true => exact Or.inl h""",
        r"""Theorem tested (P Q : Prop) :
  (P \/ Q) <-> exists b : bool, if b then P else Q.
Proof.
  split.
  - intros [HP | HQ]; [exists true | exists false]; assumption.
  - intros [b H]; destruct b; [left | right]; assumption.
Qed.""",
    ),
    (
        "22_decision_guides_search",
        r"""theorem tested (P Q : Prop) (b : Bool)
    (oracle : b = true ↔ P) (hasWitness : P ∨ Q) :
    if b then P else Q := by
  cases b with
  | false =>
      have notP : ¬ P := by
        intro hp
        have impossible := oracle.mpr hp
        cases impossible
      exact Or.resolve_left hasWitness notP
  | true => exact oracle.mp rfl""",
        r"""Theorem tested (P Q : Prop) (b : bool) :
  (b = true <-> P) -> P \/ Q -> if b then P else Q.
Proof.
  intros Horacle Hexists; destruct b.
  - apply Horacle; reflexivity.
  - destruct Hexists as [HP | HQ].
    + apply Horacle in HP; discriminate.
    + exact HQ.
Qed.""",
    ),
    (
        "23_resolution_soundness",
        r"""theorem tested (P R S : Prop) (left : P ∨ R) (right : ¬ P ∨ S) :
    R ∨ S := by
  rcases left with hp | hr
  · rcases right with hnp | hs
    · exact False.elim (hnp hp)
    · exact Or.inr hs
  · exact Or.inl hr""",
        r"""Theorem tested (P R S : Prop) :
  P \/ R -> ~ P \/ S -> R \/ S.
Proof.
  intros [HP | HR] [HNP | HS]; try tauto.
Qed.""",
    ),
    (
        "24_unit_propagation",
        r"""theorem tested (P Q : Prop) (unit : P) (clause : ¬ P ∨ Q) : Q := by
  rcases clause with hnp | hq
  · exact False.elim (hnp unit)
  · exact hq""",
        r"""Theorem tested (P Q : Prop) : P -> ~ P \/ Q -> Q.
Proof. intros HP [HNP | HQ]; [contradiction | exact HQ]. Qed.""",
    ),
    (
        "25_independent_components",
        r"""theorem tested {X Y : Type} (A : X → Prop) (B : Y → Prop) :
    (∃ x, A x) ∧ (∃ y, B y) ↔ ∃ x y, A x ∧ B y := by
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨x, y, hx, hy⟩
  · rintro ⟨x, y, hx, hy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩""",
        r"""Theorem tested (X Y : Type) (A : X -> Prop) (B : Y -> Prop) :
  (exists x, A x) /\ (exists y, B y) <-> exists x y, A x /\ B y.
Proof.
  split.
  - intros [[x HX] [y HY]]; exists x, y; split; assumption.
  - intros [x [y [HX HY]]]; split; [exists x | exists y]; assumption.
Qed.""",
    ),
    (
        "26_separator_agreement",
        r"""theorem tested :
    (∃ b : Bool, b = true) ∧ (∃ b : Bool, b = false) ∧
    ¬ (∃ b : Bool, b = true ∧ b = false) := by decide""",
        r"""Theorem tested :
  (exists b : bool, b = true) /\ (exists b : bool, b = false) /\
  ~ (exists b : bool, b = true /\ b = false).
Proof.
  split; [exists true; reflexivity | split].
  - exists false; reflexivity.
  - intros [b [HT HF]]; rewrite HT in HF; discriminate.
Qed.""",
    ),
    (
        "27_variable_elimination",
        r"""theorem tested (P Q : Prop) :
    (∃ b : Bool, (b = true ∧ P) ∨ (b = false ∧ Q)) ↔ P ∨ Q := by
  constructor
  · rintro ⟨b, h⟩
    rcases h with ⟨_, hp⟩ | ⟨_, hq⟩
    · exact Or.inl hp
    · exact Or.inr hq
  · intro h
    rcases h with hp | hq
    · exact ⟨true, Or.inl ⟨rfl, hp⟩⟩
    · exact ⟨false, Or.inr ⟨rfl, hq⟩⟩""",
        r"""Theorem tested (P Q : Prop) :
  (exists b : bool, (b = true /\ P) \/ (b = false /\ Q)) <-> P \/ Q.
Proof.
  split.
  - intros [b [[_ HP] | [_ HQ]]]; [left | right]; assumption.
  - intros [HP | HQ].
    + exists true; left; split; [reflexivity | assumption].
    + exists false; right; split; [reflexivity | assumption].
Qed.""",
    ),
    (
        "28_definitional_extension",
        r"""theorem tested (P : Prop) :
    (∃ z : Prop, (z ↔ P) ∧ z) ↔ P := by
  constructor
  · rintro ⟨_, hz, holds⟩
    exact hz.mp holds
  · intro hp
    exact ⟨P, Iff.rfl, hp⟩""",
        r"""Theorem tested (P : Prop) :
  (exists z : Prop, (z <-> P) /\ z) <-> P.
Proof.
  split.
  - intros [z [Hz Htrue]]; apply Hz; exact Htrue.
  - intro HP; exists P; split; [tauto | exact HP].
Qed.""",
    ),
    (
        "29_reduction_correctness_chain",
        r"""theorem tested {X Y : Type} (A : X → Prop) (B D : Y → Prop)
    (reduce : X → Y) (preserve : ∀ x, A x ↔ B (reduce x))
    (decideTarget : ∀ y, B y ↔ D y) :
    ∀ x, A x ↔ D (reduce x) := by
  intro x
  exact Iff.trans (preserve x) (decideTarget (reduce x))""",
        r"""Theorem tested (X Y : Type) (A : X -> Prop) (B D : Y -> Prop)
  (reduce : X -> Y) :
  (forall x, A x <-> B (reduce x)) ->
  (forall y, B y <-> D y) -> forall x, A x <-> D (reduce x).
Proof.
  intros Hreduce Hdecide x; transitivity (B (reduce x)).
  - apply Hreduce.
  - apply Hdecide.
Qed.""",
    ),
    (
        "30_lower_bound_transfer",
        r"""theorem tested {Algorithm Circuit : Type}
    (compile : Algorithm → Circuit) (fast : Algorithm → Prop)
    (correct expensive : Circuit → Prop)
    (lowerBound : ∀ c, correct c → expensive c)
    (simulation : ∀ a, fast a → correct (compile a))
    (sizeBound : ∀ a, fast a → ¬ expensive (compile a)) :
    ∀ a, ¬ fast a := by
  intro a ha
  exact (sizeBound a ha) (lowerBound (compile a) (simulation a ha))""",
        r"""Theorem tested (Algorithm Circuit : Type) (compile : Algorithm -> Circuit)
  (fast : Algorithm -> Prop) (correct expensive : Circuit -> Prop) :
  (forall c, correct c -> expensive c) ->
  (forall a, fast a -> correct (compile a)) ->
  (forall a, fast a -> ~ expensive (compile a)) ->
  forall a, ~ fast a.
Proof.
  intros Hlower Hsimulation Hsize a Hfast.
  apply (Hsize a Hfast).
  apply Hlower, Hsimulation, Hfast.
Qed.""",
    ),
    (
        "31_lengthwise_advice",
        r"""theorem tested (f : Bool → Bool) :
    ∃ table : Bool × Bool, f false = table.1 ∧ f true = table.2 := by
  exact ⟨(f false, f true), rfl, rfl⟩""",
        r"""Theorem tested (f : bool -> bool) :
  exists table : bool * bool, f false = fst table /\ f true = snd table.
Proof. exists (f false, f true); split; reflexivity. Qed.""",
    ),
    (
        "32_promise_coverage",
        r"""theorem tested :
    ∃ promise answer : Bool → Bool,
      (∀ x, promise x = true → answer x = x) ∧ answer false ≠ false := by
  refine ⟨(fun x => x), (fun _ => true), ?_, ?_⟩
  · intro x hx
    cases x <;> cases hx <;> rfl
  · decide""",
        r"""Theorem tested :
  exists promise answer : bool -> bool,
    (forall x, promise x = true -> answer x = x) /\ answer false <> false.
Proof.
  exists (fun x => x), (fun _ => true); split.
  - intros [] H; simpl in *; [reflexivity | discriminate].
  - discriminate.
Qed.""",
    ),
    (
        "33_average_vs_worst",
        r"""theorem tested :
    ∃ f : Bool × Bool → Bool,
      f (false, false) = false ∧ f (false, true) = true ∧
      f (true, false) = true ∧ f (true, true) = true := by
  exact ⟨(fun p => p.1 || p.2), by decide⟩""",
        r"""Theorem tested :
  exists f : bool * bool -> bool,
    f (false, false) = false /\ f (false, true) = true /\
    f (true, false) = true /\ f (true, true) = true.
Proof.
  exists (fun p => orb (fst p) (snd p)); repeat split; reflexivity.
Qed.""",
    ),
    (
        "34_algorithm_quantifiers",
        r"""theorem tested :
    ∃ fails : Bool → Bool → Prop,
      (∀ algorithm, ∃ input, fails algorithm input) ∧
      ¬ (∃ input, ∀ algorithm, fails algorithm input) := by
  refine ⟨(fun algorithm input => algorithm = input), ?_⟩
  decide""",
        r"""Theorem tested :
  exists fails : bool -> bool -> Prop,
    (forall algorithm, exists input, fails algorithm input) /\
    ~ (exists input, forall algorithm, fails algorithm input).
Proof.
  exists (fun algorithm input => algorithm = input); split.
  - intro algorithm; exists algorithm; reflexivity.
  - intros [input H]; specialize (H (negb input)); destruct input; discriminate.
Qed.""",
    ),
    (
        "35_exact_compression",
        r"""theorem tested {X Code : Type} (encode : X → Code) (decode : Code → X)
    (roundTrip : ∀ x, decode (encode x) = x) :
    Function.Injective encode := by
  intro x y equalCode
  calc
    x = decode (encode x) := (roundTrip x).symm
    _ = decode (encode y) := congrArg decode equalCode
    _ = y := roundTrip y""",
        r"""Theorem tested (X Code : Type) (encode : X -> Code) (decode : Code -> X) :
  (forall x, decode (encode x) = x) ->
  forall x y, encode x = encode y -> x = y.
Proof.
  intros Hround x y Hequal.
  rewrite <- (Hround x), <- (Hround y).
  now rewrite Hequal.
Qed.""",
    ),
    (
        "36_exact_rounding",
        r"""theorem tested {Discrete Relaxed : Type}
    (feasible : Discrete → Prop) (relaxed : Relaxed → Prop)
    (round : Relaxed → Discrete)
    (soundRound : ∀ y, relaxed y → feasible (round y)) :
    (∃ y, relaxed y) → ∃ x, feasible x := by
  rintro ⟨y, hy⟩
  exact ⟨round y, soundRound y hy⟩""",
        r"""Theorem tested (Discrete Relaxed : Type)
  (feasible : Discrete -> Prop) (relaxed : Relaxed -> Prop)
  (round : Relaxed -> Discrete) :
  (forall y, relaxed y -> feasible (round y)) ->
  (exists y, relaxed y) -> exists x, feasible x.
Proof.
  intros Hround [y Hy]; exists (round y); apply Hround, Hy.
Qed.""",
    ),
    (
        "37_parameter_bound",
        r"""theorem tested (cost : Nat → Nat) (k cap : Nat)
    (monotone : ∀ a b, a ≤ b → cost a ≤ cost b)
    (bounded : k ≤ cap) : cost k ≤ cost cap := by
  exact monotone k cap bounded""",
        r"""Theorem tested (cost : nat -> nat) (k cap : nat) :
  (forall a b, a <= b -> cost a <= cost b) ->
  k <= cap -> cost k <= cost cap.
Proof. intros Hmono Hbound; apply Hmono, Hbound. Qed.""",
    ),
    (
        "38_oracle_worlds",
        r"""theorem tested :
    ∃ property : Bool → Prop, property false ∧ ¬ property true := by
  refine ⟨(fun oracle => oracle = false), rfl, ?_⟩
  decide""",
        r"""Theorem tested :
  exists property : bool -> Prop, property false /\ ~ property true.
Proof.
  exists (fun oracle => oracle = false); split; [reflexivity | discriminate].
Qed.""",
    ),
    (
        "39_proof_system_scope",
        r"""theorem tested :
    ∃ weak strong : Bool → Prop,
      (∀ proof, weak proof → strong proof) ∧
      (∀ proof, ¬ weak proof) ∧ (∃ proof, strong proof) := by
  refine ⟨(fun _ => False), (fun _ => True), ?_, ?_, ?_⟩
  · intro _ impossible
    exact False.elim impossible
  · intro _ impossible
    exact impossible
  · exact ⟨false, True.intro⟩""",
        r"""Theorem tested :
  exists weak strong : bool -> Prop,
    (forall proof, weak proof -> strong proof) /\
    (forall proof, ~ weak proof) /\ (exists proof, strong proof).
Proof.
  exists (fun _ => False), (fun _ => True); split; [| split].
  - intros _ H; contradiction.
  - intros _ H; contradiction.
  - exists false; exact I.
Qed.""",
    ),
    (
        "40_size_induction",
        r"""theorem tested (P : Nat → Prop) (base : P 0)
    (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih""",
        r"""Theorem tested (P : nat -> Prop) :
  P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros Hbase Hstep n; induction n.
  - exact Hbase.
  - apply Hstep, IHn.
Qed.""",
    ),
]
