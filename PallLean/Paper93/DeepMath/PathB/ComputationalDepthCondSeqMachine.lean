import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq

/-!
# The conditional-sequencing combinator

`seqMachine` chains two machines linearly; the pair-assembly needs a *branch*: after the
compare machine, dispatch to a `p²+t` machine or a `t²+t+p` machine depending on `t < p`.
`condSeqMachine M₁ Mt Mf` is that primitive — it runs `M₁`, and at the handoff reads the
head cell (the flag `M₁` halts on) and dispatches to `Mt` (flag `true`) or `Mf` (flag
`false`), resetting the head to `0`.

Two composition theorems, `condSeq_run_true` / `condSeq_run_false`, mirror `seq_run`:
given `M₁`'s run to a halt at `⟨s₁f, p₁, T₁⟩` with halt-cell `T₁.getD p₁ = flag`, and the
chosen arm's run `T₁ ↦ T₂`, the composite reaches the chosen final configuration — halted —
at exactly the clock `t₁ + 1 + t₂`.  The freeze semantics absorbs any slack, as in
`seq_run`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CondSeqMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Run `M₁`, then branch on the halt-cell to `Mt` (flag `true`) or `Mf` (flag `false`),
head reset to `0`. -/
def condSeqMachine (M1 Mt Mf : Machine) : Machine where
  State := M1.State ⊕ (Mt.State ⊕ Mf.State)
  fin := letI := M1.fin; letI := Mt.fin; letI := Mf.fin; inferInstance
  dec := letI := M1.dec; letI := Mt.dec; letI := Mf.dec; inferInstance
  start := Sum.inl M1.start
  halt := fun s => match s with
    | .inl _ => false
    | .inr (.inl st) => Mt.halt st
    | .inr (.inr sf) => Mf.halt sf
  δ := fun s b => match s with
    | .inl s1 =>
      if M1.halt s1 then
        (if b then Sum.inr (Sum.inl Mt.start) else Sum.inr (Sum.inr Mf.start), none, 3)
      else (Sum.inl (M1.δ s1 b).1, (M1.δ s1 b).2.1, (M1.δ s1 b).2.2)
    | .inr (.inl st) =>
      (Sum.inr (Sum.inl (Mt.δ st b).1), (Mt.δ st b).2.1, (Mt.δ st b).2.2)
    | .inr (.inr sf) =>
      (Sum.inr (Sum.inr (Mf.δ sf b).1), (Mf.δ sf b).2.1, (Mf.δ sf b).2.2)
  accept := fun s => match s with
    | .inl _ => false
    | .inr (.inl st) => Mt.accept st
    | .inr (.inr sf) => Mf.accept sf

variable {M1 Mt Mf : Machine}

/-- Embed an `M₁`-configuration. -/
def inlCfg (M1 Mt Mf : Machine) (c : Cfg M1) : Cfg (condSeqMachine M1 Mt Mf) :=
  ⟨.inl c.st, c.hd, c.tp⟩

/-- Embed an `Mt`-configuration (the `true` arm). -/
def inrlCfg (M1 Mt Mf : Machine) (c : Cfg Mt) : Cfg (condSeqMachine M1 Mt Mf) :=
  ⟨.inr (.inl c.st), c.hd, c.tp⟩

/-- Embed an `Mf`-configuration (the `false` arm). -/
def inrrCfg (M1 Mt Mf : Machine) (c : Cfg Mf) : Cfg (condSeqMachine M1 Mt Mf) :=
  ⟨.inr (.inr c.st), c.hd, c.tp⟩

theorem cond_halt_inl (s : M1.State) : (condSeqMachine M1 Mt Mf).halt (Sum.inl s) = false :=
  rfl

theorem cond_halt_inrl (s : Mt.State) :
    (condSeqMachine M1 Mt Mf).halt (Sum.inr (Sum.inl s)) = Mt.halt s := rfl

theorem cond_halt_inrr (s : Mf.State) :
    (condSeqMachine M1 Mt Mf).halt (Sum.inr (Sum.inr s)) = Mf.halt s := rfl

theorem init_cond (T0 : List Bool) :
    init (condSeqMachine M1 Mt Mf) T0 = inlCfg M1 Mt Mf (init M1 T0) := rfl

/-! ### Step laws -/

theorem cond_delta_inl (s1 : M1.State) (b : Bool) (h : M1.halt s1 = false) :
    (condSeqMachine M1 Mt Mf).δ (Sum.inl s1) b
      = (Sum.inl (M1.δ s1 b).1, (M1.δ s1 b).2.1, (M1.δ s1 b).2.2) := by
  show (if M1.halt s1 then _ else _) = _
  rw [h]; simp

theorem cond_delta_handoff_true (s1 : M1.State) (h : M1.halt s1 = true) :
    (condSeqMachine M1 Mt Mf).δ (Sum.inl s1) true
      = (Sum.inr (Sum.inl Mt.start), none, 3) := by
  show (if M1.halt s1 then _ else _) = _
  rw [h]; simp

theorem cond_delta_handoff_false (s1 : M1.State) (h : M1.halt s1 = true) :
    (condSeqMachine M1 Mt Mf).δ (Sum.inl s1) false
      = (Sum.inr (Sum.inr Mf.start), none, 3) := by
  show (if M1.halt s1 then _ else _) = _
  rw [h]; simp

/-- Left phase, not halted: simulate `M₁`. -/
theorem step_cond_inl (c : Cfg M1) (h : M1.halt c.st = false) :
    step (condSeqMachine M1 Mt Mf) (inlCfg M1 Mt Mf c) = inlCfg M1 Mt Mf (step M1 c) := by
  unfold step
  rw [show (inlCfg M1 Mt Mf c).st = Sum.inl c.st from rfl, cond_halt_inl, h]
  simp only [Bool.false_eq_true, if_false]
  rw [show (inlCfg M1 Mt Mf c).tp = c.tp from rfl,
    show (inlCfg M1 Mt Mf c).hd = c.hd from rfl, cond_delta_inl c.st _ h]
  rfl

/-- Handoff on flag `true`: to `Mt.start`, head reset. -/
theorem step_cond_handoff_true (c : Cfg M1) (h : M1.halt c.st = true)
    (hb : c.tp.getD c.hd false = true) :
    step (condSeqMachine M1 Mt Mf) (inlCfg M1 Mt Mf c)
      = ⟨Sum.inr (Sum.inl Mt.start), 0, c.tp⟩ := by
  unfold step
  rw [show (inlCfg M1 Mt Mf c).st = Sum.inl c.st from rfl, cond_halt_inl]
  simp only [Bool.false_eq_true, if_false]
  rw [show (inlCfg M1 Mt Mf c).tp = c.tp from rfl,
    show (inlCfg M1 Mt Mf c).hd = c.hd from rfl, hb, cond_delta_handoff_true c.st h]
  rfl

/-- Handoff on flag `false`: to `Mf.start`, head reset. -/
theorem step_cond_handoff_false (c : Cfg M1) (h : M1.halt c.st = true)
    (hb : c.tp.getD c.hd false = false) :
    step (condSeqMachine M1 Mt Mf) (inlCfg M1 Mt Mf c)
      = ⟨Sum.inr (Sum.inr Mf.start), 0, c.tp⟩ := by
  unfold step
  rw [show (inlCfg M1 Mt Mf c).st = Sum.inl c.st from rfl, cond_halt_inl]
  simp only [Bool.false_eq_true, if_false]
  rw [show (inlCfg M1 Mt Mf c).tp = c.tp from rfl,
    show (inlCfg M1 Mt Mf c).hd = c.hd from rfl, hb, cond_delta_handoff_false c.st h]
  rfl

/-- `true`-arm simulation. -/
theorem step_cond_inrl (c : Cfg Mt) :
    step (condSeqMachine M1 Mt Mf) (inrlCfg M1 Mt Mf c) = inrlCfg M1 Mt Mf (step Mt c) := by
  by_cases h : Mt.halt c.st = true
  · have h2 : (condSeqMachine M1 Mt Mf).halt (inrlCfg M1 Mt Mf c).st = true := by
      rw [show (inrlCfg M1 Mt Mf c).st = Sum.inr (Sum.inl c.st) from rfl, cond_halt_inrl]
      exact h
    rw [step_of_halted Mt h, step_of_halted (condSeqMachine M1 Mt Mf) h2]
  · have h' : Mt.halt c.st = false := by simpa using h
    unfold step
    rw [show (inrlCfg M1 Mt Mf c).st = Sum.inr (Sum.inl c.st) from rfl, cond_halt_inrl, h']
    simp only [Bool.false_eq_true, if_false]
    rw [show (inrlCfg M1 Mt Mf c).tp = c.tp from rfl,
      show (inrlCfg M1 Mt Mf c).hd = c.hd from rfl]
    rfl

/-- `false`-arm simulation. -/
theorem step_cond_inrr (c : Cfg Mf) :
    step (condSeqMachine M1 Mt Mf) (inrrCfg M1 Mt Mf c) = inrrCfg M1 Mt Mf (step Mf c) := by
  by_cases h : Mf.halt c.st = true
  · have h2 : (condSeqMachine M1 Mt Mf).halt (inrrCfg M1 Mt Mf c).st = true := by
      rw [show (inrrCfg M1 Mt Mf c).st = Sum.inr (Sum.inr c.st) from rfl, cond_halt_inrr]
      exact h
    rw [step_of_halted Mf h, step_of_halted (condSeqMachine M1 Mt Mf) h2]
  · have h' : Mf.halt c.st = false := by simpa using h
    unfold step
    rw [show (inrrCfg M1 Mt Mf c).st = Sum.inr (Sum.inr c.st) from rfl, cond_halt_inrr, h']
    simp only [Bool.false_eq_true, if_false]
    rw [show (inrrCfg M1 Mt Mf c).tp = c.tp from rfl,
      show (inrrCfg M1 Mt Mf c).hd = c.hd from rfl]
    rfl

/-! ### Simulations -/

theorem run_cond_inrl (c : Cfg Mt) (t : ℕ) :
    run (condSeqMachine M1 Mt Mf) t (inrlCfg M1 Mt Mf c) = inrlCfg M1 Mt Mf (run Mt t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_cond_inrl, ← run_succ]

theorem run_cond_inrr (c : Cfg Mf) (t : ℕ) :
    run (condSeqMachine M1 Mt Mf) t (inrrCfg M1 Mt Mf c) = inrrCfg M1 Mt Mf (run Mf t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_cond_inrr, ← run_succ]

theorem run_cond_inl (c : Cfg M1) (t : ℕ)
    (h : ∀ t', t' < t → M1.halt (run M1 t' c).st = false) :
    run (condSeqMachine M1 Mt Mf) t (inlCfg M1 Mt Mf c) = inlCfg M1 Mt Mf (run M1 t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun t' ht' => h t' (by omega)),
      step_cond_inl _ (h t (by omega)), ← run_succ]

/-! ## The composition theorems -/

/-- The shared left-phase reduction: below `M₁`'s first halt, then the handoff. -/
private theorem cond_left (T0 T1 : List Bool) (t1 : ℕ) (s1f : M1.State) (p1 : ℕ)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1f, p1, T1⟩) (hh1 : M1.halt s1f = true) :
    ∃ nf, nf ≤ t1
      ∧ run (condSeqMachine M1 Mt Mf) nf (init (condSeqMachine M1 Mt Mf) T0)
          = inlCfg M1 Mt Mf ⟨s1f, p1, T1⟩ := by
  have hex : ∃ t, M1.halt (run M1 t (init M1 T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  have htm : M1.halt (run M1 (Nat.find hex) (init M1 T0)).st = true := Nat.find_spec hex
  have htm_le : Nat.find hex ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 (Nat.find hex) (init M1 T0) = ⟨s1f, p1, T1⟩ := by
    rw [← run_stable M1 T0 htm_le htm, h1]
  have hno : ∀ t', t' < Nat.find hex → M1.halt (run M1 t' (init M1 T0)).st = false := by
    intro t' ht'
    have := Nat.find_min hex ht'
    simpa using this
  have hs1 := run_cond_inl (M1 := M1) (Mt := Mt) (Mf := Mf) (init M1 T0) (Nat.find hex) hno
  rw [hfrozen] at hs1
  exact ⟨Nat.find hex, htm_le, by rw [init_cond]; exact hs1⟩

/-- **Composition, `true` branch.**  Halt-cell `true` dispatches to `Mt`. -/
theorem condSeq_run_true (T0 T1 T2 : List Bool) (t1 t2 : ℕ)
    (s1f : M1.State) (p1 : ℕ) (s2f : Mt.State) (p2 : ℕ)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1f, p1, T1⟩) (hh1 : M1.halt s1f = true)
    (hb : T1.getD p1 false = true)
    (h2 : run Mt t2 (init Mt T1) = ⟨s2f, p2, T2⟩) (hh2 : Mt.halt s2f = true) :
    run (condSeqMachine M1 Mt Mf) (t1 + 1 + t2) (init (condSeqMachine M1 Mt Mf) T0)
      = ⟨Sum.inr (Sum.inl s2f), p2, T2⟩ := by
  obtain ⟨nf, hnf, hleft⟩ := cond_left (Mt := Mt) (Mf := Mf) T0 T1 t1 s1f p1 h1 hh1
  have hstep := step_cond_handoff_true (M1 := M1) (Mt := Mt) (Mf := Mf)
    (⟨s1f, p1, T1⟩ : Cfg M1) hh1 hb
  have hs2 := run_cond_inrl (M1 := M1) (Mt := Mt) (Mf := Mf) (init Mt T1) t2
  rw [h2] at hs2
  have hfin : (condSeqMachine M1 Mt Mf).halt
      (inrlCfg M1 Mt Mf (⟨s2f, p2, T2⟩ : Cfg Mt)).st = true := by
    rw [show (inrlCfg M1 Mt Mf (⟨s2f, p2, T2⟩ : Cfg Mt)).st
      = Sum.inr (Sum.inl s2f) from rfl, cond_halt_inrl]
    exact hh2
  rw [show t1 + 1 + t2 = nf + (1 + (t2 + (t1 - nf))) from by omega, run_add, hleft, run_add,
    show run (condSeqMachine M1 Mt Mf) 1 (inlCfg M1 Mt Mf (⟨s1f, p1, T1⟩ : Cfg M1))
      = ⟨Sum.inr (Sum.inl Mt.start), 0, T1⟩ from by rw [run_succ, run_zero]; exact hstep,
    show (⟨Sum.inr (Sum.inl Mt.start), 0, T1⟩ : Cfg (condSeqMachine M1 Mt Mf))
      = inrlCfg M1 Mt Mf (init Mt T1) from rfl,
    run_add, hs2, run_of_halted (condSeqMachine M1 Mt Mf) hfin]
  rfl

/-- **Composition, `false` branch.**  Halt-cell `false` dispatches to `Mf`. -/
theorem condSeq_run_false (T0 T1 T2 : List Bool) (t1 t2 : ℕ)
    (s1f : M1.State) (p1 : ℕ) (s2f : Mf.State) (p2 : ℕ)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1f, p1, T1⟩) (hh1 : M1.halt s1f = true)
    (hb : T1.getD p1 false = false)
    (h2 : run Mf t2 (init Mf T1) = ⟨s2f, p2, T2⟩) (hh2 : Mf.halt s2f = true) :
    run (condSeqMachine M1 Mt Mf) (t1 + 1 + t2) (init (condSeqMachine M1 Mt Mf) T0)
      = ⟨Sum.inr (Sum.inr s2f), p2, T2⟩ := by
  obtain ⟨nf, hnf, hleft⟩ := cond_left (Mt := Mt) (Mf := Mf) T0 T1 t1 s1f p1 h1 hh1
  have hstep := step_cond_handoff_false (M1 := M1) (Mt := Mt) (Mf := Mf)
    (⟨s1f, p1, T1⟩ : Cfg M1) hh1 hb
  have hs2 := run_cond_inrr (M1 := M1) (Mt := Mt) (Mf := Mf) (init Mf T1) t2
  rw [h2] at hs2
  have hfin : (condSeqMachine M1 Mt Mf).halt
      (inrrCfg M1 Mt Mf (⟨s2f, p2, T2⟩ : Cfg Mf)).st = true := by
    rw [show (inrrCfg M1 Mt Mf (⟨s2f, p2, T2⟩ : Cfg Mf)).st
      = Sum.inr (Sum.inr s2f) from rfl, cond_halt_inrr]
    exact hh2
  rw [show t1 + 1 + t2 = nf + (1 + (t2 + (t1 - nf))) from by omega, run_add, hleft, run_add,
    show run (condSeqMachine M1 Mt Mf) 1 (inlCfg M1 Mt Mf (⟨s1f, p1, T1⟩ : Cfg M1))
      = ⟨Sum.inr (Sum.inr Mf.start), 0, T1⟩ from by rw [run_succ, run_zero]; exact hstep,
    show (⟨Sum.inr (Sum.inr Mf.start), 0, T1⟩ : Cfg (condSeqMachine M1 Mt Mf))
      = inrrCfg M1 Mt Mf (init Mf T1) from rfl,
    run_add, hs2, run_of_halted (condSeqMachine M1 Mt Mf) hfin]
  rfl

/-- The composite's final states are halted, so composed runs chain again. -/
theorem cond_halt_final_true (s2f : Mt.State) (hh2 : Mt.halt s2f = true) :
    (condSeqMachine M1 Mt Mf).halt (Sum.inr (Sum.inl s2f)) = true := by
  rw [cond_halt_inrl]; exact hh2

theorem cond_halt_final_false (s2f : Mf.State) (hh2 : Mf.halt s2f = true) :
    (condSeqMachine M1 Mt Mf).halt (Sum.inr (Sum.inr s2f)) = true := by
  rw [cond_halt_inrr]; exact hh2

end PallLean.Paper93.DeepMath.PathB.CondSeqMachine
