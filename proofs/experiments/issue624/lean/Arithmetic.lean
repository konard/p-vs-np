import proofs.experiments.issue624.lean.RegisterMachine

/-! Arithmetic macros for the formula generator. Every macro expands to the
existing charged register compiler; there are no additional machine primitives. -/
namespace Issue624.RegisterMachine
open Complexity Issue532.Machines

def mulProgram (a b dest : Nat) : Program :=
  let counter := subCounter a b dest
  let scratch := subScratch a b dest
  .sequence (.clearRegister counter)
    (.sequence (addToProgram a counter scratch)
      (.sequence (.clearRegister dest) (.loop counter (addToProgram b dest scratch))))

def positiveProgram (counter dest : Nat) : Program :=
  .sequence (.clearRegister dest)
    (.loop counter (.sequence (.clearRegister dest) (.straight (.increment dest 1))))

def ltProgram (a b dest : Nat) : Program :=
  let counter := subCounter a b dest
  .sequence (subProgram b a counter) (positiveProgram counter dest)

def zeroPairProgram (counter other dest : Nat) : Program :=
  .sequence (.clearRegister dest)
    (.sequence (.straight (.increment dest 1))
      (.sequence (.loop counter (.clearRegister dest)) (.loop other (.clearRegister dest))))

def eqProgram (a b dest : Nat) : Program :=
  let counter := subCounter a b dest
  .sequence (subProgram a b counter)
    (.sequence (subProgram b a (counter+3))
      (zeroPairProgram counter (counter+3) dest))

theorem mulProgram_wellFormed (k a b dest : Nat) (hk : subScratch a b dest < k)
    (hbd : b ≠ dest) : ProgramWellFormed k (mulProgram a b dest) := by
  have hw := subCounter_wider a b dest
  simp only [subScratch] at hk
  simp [mulProgram, addToProgram, ProgramWellFormed, ProgramReadOnly,
    WellFormed, ReadOnly, subScratch]
  omega

theorem positiveProgram_wellFormed (k counter dest : Nat)
    (hc : counter < k) (hd : dest < k) (hcd : counter ≠ dest) :
    ProgramWellFormed k (positiveProgram counter dest) := by
  simp [positiveProgram, ProgramWellFormed, ProgramReadOnly, WellFormed, ReadOnly, hc, hd, hcd]

theorem arithmetic_scratch (a b dest : Nat) :
    subCounter b a (subCounter a b dest) = subCounter a b dest + 1 ∧
    subScratch b a (subCounter a b dest) = subCounter a b dest + 2 ∧
    subCounter a b (subCounter a b dest) = subCounter a b dest + 1 ∧
    subScratch a b (subCounter a b dest) = subCounter a b dest + 2 ∧
    subCounter b a (subCounter a b dest+3) = subCounter a b dest + 4 ∧
    subScratch b a (subCounter a b dest+3) = subCounter a b dest + 5 := by
  have h := subCounter_wider a b dest
  simp only [subCounter, subScratch] at *
  omega

theorem ltProgram_wellFormed (k a b dest : Nat) (hk : subCounter a b dest + 2 < k) :
    ProgramWellFormed k (ltProgram a b dest) := by
  have hw := subCounter_wider a b dest
  have hh := arithmetic_scratch a b dest
  exact ⟨subProgram_wellFormed k b a _ (by omega) (by omega),
    positiveProgram_wellFormed k _ dest (by omega) (by omega) (by omega)⟩

theorem eqProgram_wellFormed (k a b dest : Nat) (hk : subCounter a b dest + 5 < k) :
    ProgramWellFormed k (eqProgram a b dest) := by
  have hw := subCounter_wider a b dest
  have hh := arithmetic_scratch a b dest
  refine ⟨subProgram_wellFormed k a b _ (by omega) (by omega),
    subProgram_wellFormed k b a _ (by omega) (by omega), ?_⟩
  simp [zeroPairProgram, ProgramWellFormed, ProgramReadOnly, WellFormed]; omega

theorem loopRun_addTo (counter source dest scratch : Nat)
    (hcs : counter ≠ source) (hcd : counter ≠ dest) (hcc : counter ≠ scratch)
    (hsd : source ≠ dest) (hsc : source ≠ scratch) (hdc : dest ≠ scratch)
    (n : Nat) (st : State) (hc : counter < st.regs.length)
    (hs : source < st.regs.length) (hd : dest < st.regs.length) (ht : scratch < st.regs.length)
    (hn : registerAt counter st = n) (hz : registerAt scratch st = 0) (slot : Nat) :
    registerAt slot (loopRun counter (programRun (addToProgram source dest scratch)) n st) =
      if slot = counter ∨ slot = scratch then 0 else
      if slot = dest then registerAt dest st + n * registerAt source st else registerAt slot st := by
  induction n generalizing st with
  | zero =>
    simp only [loopRun, Nat.zero_mul, Nat.add_zero]
    by_cases h : slot = counter ∨ slot = scratch
    · rcases h with h | h <;> subst slot <;> simp_all
    · simp only [ite_eq_right h]
      split <;> simp_all
  | succ n ih =>
    let lower := putRegister counter n st
    let next := programRun (addToProgram source dest scratch) lower
    have hl : lower.regs.length = st.regs.length := putRegister_length _ _ _
    have hlen : next.regs.length = st.regs.length := (programRun_regs_length _ _).trans hl
    have hh (i : Nat) : registerAt i next =
        if i = scratch then 0 else if i = dest then registerAt dest st + registerAt source st else
        if i = counter then n else registerAt i st := by
      rw [addToProgram_registers source dest scratch lower (by omega) (by omega) (by omega) hsd hsc hdc]
      change (if i = scratch then 0 else if i = dest then
        registerAt dest lower + registerAt source lower else registerAt i lower) = _
      rw [show registerAt dest lower = registerAt dest st from
        registerAt_putRegister_other dest counter n st (Ne.symm hcd),
        show registerAt source lower = registerAt source st from
        registerAt_putRegister_other source counter n st (Ne.symm hcs)]
      split <;> try rfl
      split <;> try rfl
      split
      · rename_i he; subst i; exact registerAt_putRegister _ _ _ hc
      · exact registerAt_putRegister_other _ _ _ _ (by assumption)
    have hcn : registerAt counter next = n := by simp [hh, hcc, hcd]
    have hsz : registerAt scratch next = 0 := by simp [hh]
    have h := ih next (by omega) (by omega) (by omega) (by omega) hcn hsz
    change registerAt slot (loopRun counter (programRun (addToProgram source dest scratch)) n next) = _
    rw [h, hh, hh]
    by_cases he : slot = counter ∨ slot = scratch
    · simp [he]
    · have hc' : slot ≠ counter := fun h => he (Or.inl h)
      have hs' : slot ≠ scratch := fun h => he (Or.inr h)
      by_cases hed : slot = dest
      · subst slot
        simp [Ne.symm hcd, hdc, hsc, hsd, Ne.symm hcs, Nat.succ_mul]
        omega
      · simp [hh, hc', hs', hed]

theorem mulProgram_registers (a b dest : Nat) (st : State)
    (hk : subScratch a b dest < st.regs.length) (hbd : b ≠ dest) (slot : Nat) :
    registerAt slot (programRun (mulProgram a b dest) st) =
      if slot = subCounter a b dest ∨ slot = subScratch a b dest then 0 else
      if slot = dest then registerAt a st * registerAt b st else registerAt slot st := by
  let counter := subCounter a b dest
  let scratch := subScratch a b dest
  have hw := subCounter_wider a b dest
  have hc : counter < scratch := by simp [counter, scratch, subScratch]
  have hs : scratch < st.regs.length := hk
  let initial := putRegister counter 0 st
  let captured := programRun (addToProgram a counter scratch) initial
  let copied := putRegister dest 0 captured
  have hlen : copied.regs.length = st.regs.length := by
    simp [copied, captured, initial, programRun_regs_length, putRegister_length]
  have hcap (i : Nat) : registerAt i captured =
      if i = scratch then 0 else if i = counter then registerAt a st else registerAt i st := by
    rw [addToProgram_registers a counter scratch initial (by simp [initial, putRegister_length]; omega)
      (by simp [initial, putRegister_length]; omega) (by simp [initial, putRegister_length]; omega)
      (by omega) (by omega) (by omega)]
    simp only [initial, registerAt_putRegister_other a counter 0 st (by omega),
      registerAt_putRegister counter 0 st (by omega), Nat.zero_add]
    split <;> try rfl
    split <;> try rfl
    exact registerAt_putRegister_other _ _ _ _ (by assumption)
  have hcopy (i : Nat) : registerAt i copied =
      if i = dest then 0 else if i = scratch then 0 else
      if i = counter then registerAt a st else registerAt i st := by
    by_cases he : i = dest
    · subst i
      simp only [ite_true]
      exact registerAt_putRegister dest 0 captured (by simp [captured, initial, programRun_regs_length, putRegister_length]; omega)
    · simp [copied, registerAt_putRegister_other _ _ _ _ he, hcap, he]
  change registerAt slot (loopRun counter (programRun (addToProgram b dest scratch))
    (registerAt counter copied) copied) = _
  rw [loopRun_addTo counter b dest scratch (by omega) (by omega) (by omega) hbd (by omega) (by omega)
    _ copied (by omega) (by omega) (by omega) (by omega) rfl (by simp [hcopy, show scratch ≠ dest by omega])]
  have hbc : b ≠ counter := by omega
  have hbs : b ≠ scratch := by omega
  have hcd : counter ≠ dest := by omega
  have hds : dest ≠ scratch := by omega
  simp only [hcopy, ite_eq_right hbd, ite_eq_right hbc, ite_eq_right hbs,
    ite_eq_right hcd, ite_eq_right (show counter ≠ scratch by omega), ite_eq_right hds, ite_true,
    Nat.zero_add]
  by_cases he : slot = counter ∨ slot = scratch
  · simp [he, counter, scratch]
  · simp only [ite_eq_right he]
    have hsc : slot ≠ counter := fun h => he (Or.inl h)
    have hss : slot ≠ scratch := fun h => he (Or.inr h)
    dsimp [counter, scratch] at hsc hss hds hcd
    by_cases hed : slot = dest <;> simp [hsc, hss, hed, counter, scratch, hds, Ne.symm hcd]

theorem mulProgram_out (a b dest : Nat) (st : State) :
    (programRun (mulProgram a b dest) st).out = st.out := by
  simp only [mulProgram, programRun]
  rw [loopRun_out _ _ (addToProgram_out b dest _)]
  change (programRun (addToProgram a _ _) (putRegister _ 0 st)).out = st.out
  rw [addToProgram_out]; rfl

theorem mulProgram_reaches (x : Word) (k a b dest : Nat) (st : State)
    (hk : st.regs.length = k) (hs : subScratch a b dest < k) (hbd : b ≠ dest) :
    ∃ c, Reaches (compileProgram k (mulProgram a b dest)) (encode 0 x st)
      (programCost x (mulProgram a b dest) st) c ∧
      Similar (encode (compileProgram k (mulProgram a b dest)).program.length x
        (programRun (mulProgram a b dest) st)) c :=
  compileProgram_reaches x k _ st (mulProgram_wellFormed k a b dest hs hbd) hk

theorem loopRun_constant (counter dest value : Nat) (body : State → State)
    (hcd : counter ≠ dest) (hr : ∀ s, (body s).regs.length = s.regs.length)
    (hb : ∀ s, dest < s.regs.length → ∀ i, registerAt i (body s) =
      if i = dest then value else registerAt i s)
    (n : Nat) (st : State) (hc : counter < st.regs.length) (hd : dest < st.regs.length)
    (hn : registerAt counter st = n) (slot : Nat) :
    registerAt slot (loopRun counter body n st) =
      if slot = counter then 0 else if slot = dest then
      (if n = 0 then registerAt dest st else value) else registerAt slot st := by
  induction n generalizing st with
  | zero =>
    simp only [loopRun, ite_true]
    by_cases he : slot = counter
    · subst slot; simp [hn]
    · simp only [ite_eq_right he]; split <;> simp_all
  | succ n ih =>
    let lower := putRegister counter n st
    let next := body lower
    have hl : lower.regs.length = st.regs.length := putRegister_length _ _ _
    have hlen : next.regs.length = st.regs.length := (hr lower).trans hl
    have hh (i : Nat) : registerAt i next =
        if i = dest then value else if i = counter then n else registerAt i st := by
      rw [hb lower (by omega)]
      split <;> try rfl
      split
      · rename_i he; subst i; exact registerAt_putRegister _ _ _ hc
      · exact registerAt_putRegister_other _ _ _ _ (by assumption)
    have hcn : registerAt counter next = n := by simp [hh, hcd]
    change registerAt slot (loopRun counter body n next) = _
    rw [ih next (by omega) (by omega) hcn]
    by_cases he : slot = counter
    · simp [he]
    · by_cases hed : slot = dest
      · subst slot; simp [hh, Ne.symm hcd]
      · simp [he, hed, hh]

theorem setFlag_registers (dest : Nat) (st : State) (hd : dest < st.regs.length) (slot : Nat) :
    registerAt slot (programRun (.sequence (.clearRegister dest) (.straight (.increment dest 1))) st) =
      if slot = dest then 1 else registerAt slot st := by
  by_cases he : slot = dest
  · subst slot
    simp only [programRun, ite_true]
    rw [incrementRegs_registerAt dest 1 _ (by simpa [putRegister_length] using hd),
      registerAt_putRegister dest 0 st hd]
  · rw [ite_eq_right he]
    exact (programRun_readOnly slot _ st ⟨he, he⟩)

theorem positiveProgram_registers (counter dest : Nat) (st : State)
    (hc : counter < st.regs.length) (hd : dest < st.regs.length) (hcd : counter ≠ dest) (slot : Nat) :
    registerAt slot (programRun (positiveProgram counter dest) st) =
      if slot = counter then 0 else if slot = dest then
      (if registerAt counter st = 0 then 0 else 1) else registerAt slot st := by
  let initial := putRegister dest 0 st
  have hl : initial.regs.length = st.regs.length := putRegister_length _ _ _
  change registerAt slot (loopRun counter
    (programRun (.sequence (.clearRegister dest) (.straight (.increment dest 1))))
    (registerAt counter initial) initial) = _
  rw [loopRun_constant counter dest 1 _ hcd (programRun_regs_length _)
    (setFlag_registers dest) _ initial (by omega) (by omega) rfl]
  rw [show registerAt counter initial = registerAt counter st from
    registerAt_putRegister_other counter dest 0 st hcd]
  rw [show registerAt dest initial = 0 from registerAt_putRegister _ _ _ hd]
  by_cases he : slot = counter
  · simp [he]
  · by_cases hed : slot = dest
    · simp [hed]
    · simp [he, hed, initial, registerAt_putRegister_other _ _ _ _ hed]

theorem positiveProgram_out (counter dest : Nat) (st : State) :
    (programRun (positiveProgram counter dest) st).out = st.out := by
  simp only [positiveProgram, programRun]
  rw [loopRun_out counter (fun s => runProg (.increment dest 1) (putRegister dest 0 s))
    (fun _ => rfl)]; rfl

theorem ltProgram_registers (a b dest : Nat) (st : State)
    (hk : subCounter a b dest + 2 < st.regs.length) (slot : Nat) :
    registerAt slot (programRun (ltProgram a b dest) st) =
      if subCounter a b dest ≤ slot ∧ slot ≤ subCounter a b dest + 2 then 0 else
      if slot = dest then (if registerAt a st < registerAt b st then 1 else 0) else registerAt slot st := by
  let counter := subCounter a b dest
  let diff := programRun (subProgram b a counter) st
  have hw := subCounter_wider a b dest
  have hh := arithmetic_scratch a b dest
  have hs : subScratch b a counter = counter + 2 := hh.2.1
  have hce : subCounter b a counter = counter + 1 := hh.1
  have hl : diff.regs.length = st.regs.length := programRun_regs_length _ _
  have hd (i : Nat) : registerAt i diff =
      if i = counter+1 ∨ i = counter+2 then 0 else
      if i = counter then registerAt b st - registerAt a st else registerAt i st := by
    have h := subProgram_registers b a counter st (by rw [hs]; exact hk) (by omega) i
    rw [hce, hs] at h
    exact h
  change registerAt slot (programRun (positiveProgram counter dest) diff) = _
  rw [positiveProgram_registers counter dest diff (by omega) (by omega) (by omega), hd, hd]
  by_cases hsc : slot = counter
  · subst slot; simp [counter]
  · by_cases hsd : slot = dest
    · subst slot
      have hf : ¬(counter ≤ dest ∧ dest ≤ counter+2) := by omega
      simp only [ite_eq_right hsc, ite_true]
      rw [ite_eq_right (by omega : ¬(counter = counter+1 ∨ counter = counter+2)), ite_eq_right hf]
      change (if registerAt b st - registerAt a st = 0 then 0 else 1) = _
      by_cases hlt : registerAt a st < registerAt b st
      · simp [hlt, show registerAt b st - registerAt a st ≠ 0 by omega]
      · simp [hlt, show registerAt b st - registerAt a st = 0 by omega]
    · simp only [ite_eq_right hsc, ite_eq_right hsd]
      change (if slot = counter+1 ∨ slot = counter+2 then 0 else registerAt slot st) =
        (if counter ≤ slot ∧ slot ≤ counter+2 then 0 else registerAt slot st)
      by_cases he : slot = counter+1 ∨ slot = counter+2
      · rw [ite_eq_left he, ite_eq_left (by omega)]
      · rw [ite_eq_right he, ite_eq_right (by omega)]

theorem ltProgram_out (a b dest : Nat) (st : State) :
    (programRun (ltProgram a b dest) st).out = st.out := by
  rw [ltProgram, programRun, positiveProgram_out, subProgram_out]

theorem ltProgram_reaches (x : Word) (k a b dest : Nat) (st : State)
    (hk : st.regs.length = k) (hs : subCounter a b dest + 2 < k) :
    ∃ c, Reaches (compileProgram k (ltProgram a b dest)) (encode 0 x st)
      (programCost x (ltProgram a b dest) st) c ∧
      Similar (encode (compileProgram k (ltProgram a b dest)).program.length x
        (programRun (ltProgram a b dest) st)) c :=
  compileProgram_reaches x k _ st (ltProgram_wellFormed k a b dest hs) hk

theorem clearLoop_registers (counter dest : Nat) (st : State)
    (hc : counter < st.regs.length) (hd : dest < st.regs.length) (hcd : counter ≠ dest) (slot : Nat) :
    registerAt slot (programRun (.loop counter (.clearRegister dest)) st) =
      if slot = counter then 0 else if slot = dest then
      (if registerAt counter st = 0 then registerAt dest st else 0) else registerAt slot st := by
  apply loopRun_constant counter dest 0 (programRun (.clearRegister dest)) hcd
    (programRun_regs_length _) _ _ st hc hd rfl
  intro s hs i
  by_cases he : i = dest
  · subst i; simp only [ite_true]; exact registerAt_putRegister dest 0 s hs
  · rw [ite_eq_right he]; exact registerAt_putRegister_other i dest 0 s he

private theorem zeroPair_value (counter other dest slot n m value : Nat)
    (hco : counter ≠ other) (hcd : counter ≠ dest) (_hod : other ≠ dest) :
    (if slot = other then 0 else if slot = dest then
      (if m = 0 then (if n = 0 then 1 else 0) else 0) else
      if slot = counter then 0 else if slot = dest then (if n = 0 then 1 else 0) else
      if slot = dest then 1 else value) =
    (if slot = counter ∨ slot = other then 0 else if slot = dest then
      (if n = 0 ∧ m = 0 then 1 else 0) else value) := by
  by_cases hs : slot = counter <;> by_cases ho : slot = other <;> by_cases hd : slot = dest <;>
    by_cases hn : n = 0 <;> by_cases hm : m = 0 <;> simp_all

private theorem eqResult_value (counter dest slot a b value : Nat) (hd : dest < counter) :
    (if slot = counter ∨ slot = counter+3 then 0 else if slot = dest then
      (if a-b = 0 ∧ b-a = 0 then 1 else 0) else
      if slot = counter+4 ∨ slot = counter+5 then 0 else
      if slot = counter+3 then b-a else if slot = counter+1 ∨ slot = counter+2 then 0 else
      if slot = counter then a-b else value) =
    (if counter ≤ slot ∧ slot ≤ counter+5 then 0 else
      if slot = dest then (if a = b then 1 else 0) else value) := by
  have he : a-b = 0 ∧ b-a = 0 ↔ a = b := by omega
  simp only [he]
  by_cases hs : slot = dest
  · subst slot
    simp only [ite_eq_right (by omega : ¬(dest = counter ∨ dest = counter+3)), ite_true,
      ite_eq_right (by omega : ¬(counter ≤ dest ∧ dest ≤ counter+5))]
  · simp only [ite_eq_right hs]
    by_cases h3 : slot = counter+3 <;> by_cases h0 : slot = counter <;>
      by_cases h45 : slot = counter+4 ∨ slot = counter+5 <;>
      by_cases h12 : slot = counter+1 ∨ slot = counter+2 <;>
      simp only [h3, h0, h45, h12, or_self, or_true, true_or, ite_true, ite_false] <;>
      first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]

theorem zeroPairProgram_registers (counter other dest : Nat) (st : State)
    (hc : counter < st.regs.length) (ho : other < st.regs.length) (hd : dest < st.regs.length)
    (hco : counter ≠ other) (hcd : counter ≠ dest) (hod : other ≠ dest) (slot : Nat) :
    registerAt slot (programRun (zeroPairProgram counter other dest) st) =
      if slot = counter ∨ slot = other then 0 else
      if slot = dest then
      (if registerAt counter st = 0 ∧ registerAt other st = 0 then 1 else 0) else registerAt slot st := by
  let flagged := programRun (.sequence (.clearRegister dest) (.straight (.increment dest 1))) st
  let first := programRun (.loop counter (.clearRegister dest)) flagged
  have hf (i : Nat) : registerAt i flagged = if i = dest then 1 else registerAt i st :=
    setFlag_registers dest st hd i
  have hlf : flagged.regs.length = st.regs.length := programRun_regs_length _ _
  have hll : first.regs.length = st.regs.length := (programRun_regs_length _ _).trans hlf
  have hfirst (i : Nat) : registerAt i first =
      if i = counter then 0 else if i = dest then
      (if registerAt counter st = 0 then 1 else 0) else registerAt i flagged := by
    rw [clearLoop_registers counter dest flagged (by omega) (by omega) hcd i, hf counter, hf dest]
    simp only [ite_eq_right hcd, ite_true]
  have hv : registerAt other first = registerAt other st := by
    rw [hfirst other, hf other]
    simp only [ite_eq_right (Ne.symm hco), ite_eq_right hod]
  have hdv : registerAt dest first = if registerAt counter st = 0 then 1 else 0 := by
    rw [hfirst dest]
    simp only [ite_eq_right (Ne.symm hcd), ite_true]
  change registerAt slot (programRun (.loop other (.clearRegister dest)) first) = _
  rw [clearLoop_registers other dest first (by omega) (by omega) hod slot, hv, hdv, hfirst slot, hf slot]
  exact zeroPair_value counter other dest slot (registerAt counter st) (registerAt other st)
    (registerAt slot st) hco hcd hod

theorem zeroPairProgram_out (counter other dest : Nat) (st : State) :
    (programRun (zeroPairProgram counter other dest) st).out = st.out := by
  unfold zeroPairProgram
  simp only [programRun]
  rw [loopRun_out other (fun s => putRegister dest 0 s) (fun _ => rfl)]
  rw [loopRun_out counter (fun s => putRegister dest 0 s) (fun _ => rfl)]
  rfl

theorem eqProgram_registers (a b dest : Nat) (st : State)
    (hk : subCounter a b dest + 5 < st.regs.length) (slot : Nat) :
    registerAt slot (programRun (eqProgram a b dest) st) =
      if subCounter a b dest ≤ slot ∧ slot ≤ subCounter a b dest + 5 then 0 else
      if slot = dest then (if registerAt a st = registerAt b st then 1 else 0) else registerAt slot st := by
  let counter := subCounter a b dest
  let diff1 := programRun (subProgram a b counter) st
  let diff2 := programRun (subProgram b a (counter+3)) diff1
  have hw := subCounter_wider a b dest
  have hh := arithmetic_scratch a b dest
  have he1 : subCounter a b counter = counter+1 := hh.2.2.1
  have he2 : subScratch a b counter = counter+2 := hh.2.2.2.1
  have he3 : subCounter b a (counter+3) = counter+4 := hh.2.2.2.2.1
  have he4 : subScratch b a (counter+3) = counter+5 := hh.2.2.2.2.2
  have hl1 : diff1.regs.length = st.regs.length := programRun_regs_length _ _
  have hl2 : diff2.regs.length = st.regs.length := (programRun_regs_length _ _).trans hl1
  have h1 (i : Nat) : registerAt i diff1 =
      if i = counter+1 ∨ i = counter+2 then 0 else
      if i = counter then registerAt a st - registerAt b st else registerAt i st := by
    have h := subProgram_registers a b counter st (by rw [he2]; omega) (by omega) i
    rw [he1, he2] at h; exact h
  have h2 (i : Nat) : registerAt i diff2 =
      if i = counter+4 ∨ i = counter+5 then 0 else
      if i = counter+3 then registerAt b st - registerAt a st else registerAt i diff1 := by
    have h := subProgram_registers b a (counter+3) diff1 (by rw [he4, hl1]; omega) (by omega) i
    rw [he3, he4, h1 b, h1 a] at h
    simpa only [ite_eq_right (by omega : ¬(b = counter+1 ∨ b = counter+2)),
      ite_eq_right (by omega : b ≠ counter),
      ite_eq_right (by omega : ¬(a = counter+1 ∨ a = counter+2)),
      ite_eq_right (by omega : a ≠ counter)] using h
  change registerAt slot (programRun (zeroPairProgram counter (counter+3) dest) diff2) = _
  rw [zeroPairProgram_registers counter (counter+3) dest diff2 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) slot]
  have hv1 : registerAt counter diff2 = registerAt a st - registerAt b st := by
    rw [h2 counter, h1 counter]
    simp only [ite_eq_right (by omega : ¬(counter = counter+4 ∨ counter = counter+5)),
      ite_eq_right (by omega : counter ≠ counter+3),
      ite_eq_right (by omega : ¬(counter = counter+1 ∨ counter = counter+2)), ite_true]
  have hv2 : registerAt (counter+3) diff2 = registerAt b st - registerAt a st := by
    rw [h2 (counter+3)]
    simp only [ite_eq_right (by omega : ¬(counter+3 = counter+4 ∨ counter+3 = counter+5)), ite_true]
  rw [hv1, hv2]
  rw [h2 slot, h1 slot]
  exact eqResult_value counter dest slot (registerAt a st) (registerAt b st) (registerAt slot st) hw.2.2

theorem eqProgram_out (a b dest : Nat) (st : State) :
    (programRun (eqProgram a b dest) st).out = st.out := by
  rw [eqProgram, programRun, programRun, zeroPairProgram_out, subProgram_out, subProgram_out]

theorem eqProgram_reaches (x : Word) (k a b dest : Nat) (st : State)
    (hk : st.regs.length = k) (hs : subCounter a b dest + 5 < k) :
    ∃ c, Reaches (compileProgram k (eqProgram a b dest)) (encode 0 x st)
      (programCost x (eqProgram a b dest) st) c ∧
      Similar (encode (compileProgram k (eqProgram a b dest)).program.length x
        (programRun (eqProgram a b dest) st)) c :=
  compileProgram_reaches x k _ st (eqProgram_wellFormed k a b dest hs) hk

/-- Both branches consume their flag, and bodies preserve the private flags. -/
def branchProgram (flag alternative : Nat) (yes no : Program) : Program :=
  .sequence (.sequence (.clearRegister alternative) (.straight (.increment alternative 1)))
    (.sequence (.loop flag (.sequence (.clearRegister alternative) yes)) (.loop alternative no))

def ifLtProgram (a b flag alternative : Nat) (yes no : Program) : Program :=
  .sequence (ltProgram a b flag) (branchProgram flag alternative yes no)

def selectEqProgram (a b flag alternative : Nat) (yes no : Program) : Program :=
  .sequence (eqProgram a b flag) (branchProgram flag alternative yes no)

theorem state_register_ext (st next : State) (hl : st.regs.length = next.regs.length)
    (ho : st.out = next.out) (hv : ∀ i, registerAt i st = registerAt i next) : st = next := by
  have hr : st.regs = next.regs := List.ext_getElem hl (by
    intro i hi hj
    simpa only [registerAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] using hv i)
  cases st; cases next; cases hr; cases ho; rfl

theorem putRegister_overwrite (slot value old : Nat) (st : State) :
    putRegister slot value (putRegister slot old st) = putRegister slot value st := by
  cases st
  simp only [putRegister, List.set_set]

theorem putRegister_commute (slot other value old : Nat) (st : State) (h : slot ≠ other) :
    putRegister slot value (putRegister other old st) =
    putRegister other old (putRegister slot value st) := by
  cases st
  simp only [putRegister]
  congr 1
  exact List.set_comm old value (Ne.symm h)

theorem setFlag_state (dest : Nat) (st : State) (hd : dest < st.regs.length) :
    programRun (.sequence (.clearRegister dest) (.straight (.increment dest 1))) st =
      putRegister dest 1 st := by
  apply state_register_ext _ _ ((programRun_regs_length _ _).trans (putRegister_length _ _ _).symm) rfl
  intro i
  rw [setFlag_registers dest st hd i]
  by_cases he : i = dest
  · subst i; simp only [ite_true]; exact (registerAt_putRegister dest 1 st hd).symm
  · rw [ite_eq_right he, registerAt_putRegister_other i dest 1 st he]

theorem branchProgram_wellFormed (k flag alternative : Nat) (yes no : Program)
    (hf : flag < k) (ha : alternative < k) (hne : flag ≠ alternative)
    (hy : ProgramWellFormed k yes) (hn : ProgramWellFormed k no)
    (hyf : ProgramReadOnly flag yes) (_hya : ProgramReadOnly alternative yes)
    (hna : ProgramReadOnly alternative no) : ProgramWellFormed k (branchProgram flag alternative yes no) := by
  exact ⟨⟨ha, ha⟩, ⟨hf, ⟨ha, hy⟩, ⟨hne, hyf⟩⟩, ⟨ha, hn, hna⟩⟩

theorem branchProgram_run (flag alternative : Nat) (yes no : Program) (st : State)
    (_hf : flag < st.regs.length) (ha : alternative < st.regs.length) (hne : flag ≠ alternative)
    (hbit : registerAt flag st ≤ 1) (hya : ProgramReadOnly alternative yes) :
    programRun (branchProgram flag alternative yes no) st =
      if registerAt flag st = 0 then programRun no (putRegister alternative 0 st) else
      programRun yes (putRegister alternative 0 (putRegister flag 0 st)) := by
  rw [branchProgram, programRun, setFlag_state alternative st ha]
  have hflag : registerAt flag (putRegister alternative 1 st) = registerAt flag st :=
    registerAt_putRegister_other flag alternative 1 st hne
  by_cases hz : registerAt flag st = 0
  · simp only [programRun, hflag, hz, loopRun, ite_true]
    rw [registerAt_putRegister alternative 1 st ha, loopRun, loopRun, putRegister_overwrite]
  · have hone : registerAt flag st = 1 := by omega
    simp only [programRun, hflag, hone, loopRun, Nat.one_ne_zero, ite_false]
    rw [putRegister_commute flag alternative 0 1 st hne, putRegister_overwrite]
    have hzero : registerAt alternative
        (programRun yes (putRegister alternative 0 (putRegister flag 0 st))) = 0 := by
      rw [programRun_readOnly alternative yes _ hya,
        registerAt_putRegister alternative 0 _ (by simpa only [putRegister_length] using ha)]
    rw [hzero, loopRun]

theorem branchProgram_reaches (x : Word) (k flag alternative : Nat) (yes no : Program) (st : State)
    (hk : st.regs.length = k) (hw : ProgramWellFormed k (branchProgram flag alternative yes no)) :
    ∃ c, Reaches (compileProgram k (branchProgram flag alternative yes no)) (encode 0 x st)
      (programCost x (branchProgram flag alternative yes no) st) c ∧
      Similar (encode (compileProgram k (branchProgram flag alternative yes no)).program.length x
        (programRun (branchProgram flag alternative yes no) st)) c :=
  compileProgram_reaches x k _ st hw hk

theorem ifLtProgram_run (a b flag alternative : Nat) (yes no : Program) (st : State)
    (hk : subCounter a b flag+2 < st.regs.length) (ha : alternative < st.regs.length)
    (hne : flag ≠ alternative) (hya : ProgramReadOnly alternative yes) :
    programRun (ifLtProgram a b flag alternative yes no) st =
      let compared := programRun (ltProgram a b flag) st
      if registerAt a st < registerAt b st then
        programRun yes (putRegister alternative 0 (putRegister flag 0 compared)) else
        programRun no (putRegister alternative 0 compared) := by
  let compared := programRun (ltProgram a b flag) st
  have hw := subCounter_wider a b flag
  have hl : compared.regs.length = st.regs.length := programRun_regs_length _ _
  have hf : registerAt flag compared = if registerAt a st < registerAt b st then 1 else 0 := by
    have h := ltProgram_registers a b flag st hk flag
    simpa only [ite_eq_right (by omega : ¬(subCounter a b flag ≤ flag ∧ flag ≤ subCounter a b flag+2)),
      ite_true] using h
  change programRun (branchProgram flag alternative yes no) compared = _
  rw [branchProgram_run flag alternative yes no compared (by omega) (by omega) hne
    (by rw [hf]; split <;> omega) hya, hf]
  split <;> simp only [Nat.one_ne_zero, ite_false, ite_true] <;> rfl

theorem selectEqProgram_run (a b flag alternative : Nat) (yes no : Program) (st : State)
    (hk : subCounter a b flag+5 < st.regs.length) (ha : alternative < st.regs.length)
    (hne : flag ≠ alternative) (hya : ProgramReadOnly alternative yes) :
    programRun (selectEqProgram a b flag alternative yes no) st =
      let compared := programRun (eqProgram a b flag) st
      if registerAt a st = registerAt b st then
        programRun yes (putRegister alternative 0 (putRegister flag 0 compared)) else
        programRun no (putRegister alternative 0 compared) := by
  let compared := programRun (eqProgram a b flag) st
  have hw := subCounter_wider a b flag
  have hl : compared.regs.length = st.regs.length := programRun_regs_length _ _
  have hf : registerAt flag compared = if registerAt a st = registerAt b st then 1 else 0 := by
    have h := eqProgram_registers a b flag st hk flag
    simpa only [ite_eq_right (by omega : ¬(subCounter a b flag ≤ flag ∧ flag ≤ subCounter a b flag+5)),
      ite_true] using h
  change programRun (branchProgram flag alternative yes no) compared = _
  rw [branchProgram_run flag alternative yes no compared (by omega) (by omega) hne
    (by rw [hf]; split <;> omega) hya, hf]
  split <;> simp only [Nat.one_ne_zero, ite_false, ite_true] <;> rfl

theorem ifLtProgram_wellFormed (k a b flag alternative : Nat) (yes no : Program)
    (hc : subCounter a b flag + 2 < k) (hb : ProgramWellFormed k (branchProgram flag alternative yes no)) :
    ProgramWellFormed k (ifLtProgram a b flag alternative yes no) :=
  ⟨ltProgram_wellFormed k a b flag hc, hb⟩

theorem selectEqProgram_wellFormed (k a b flag alternative : Nat) (yes no : Program)
    (hc : subCounter a b flag + 5 < k) (hb : ProgramWellFormed k (branchProgram flag alternative yes no)) :
    ProgramWellFormed k (selectEqProgram a b flag alternative yes no) :=
  ⟨eqProgram_wellFormed k a b flag hc, hb⟩

end Issue624.RegisterMachine
