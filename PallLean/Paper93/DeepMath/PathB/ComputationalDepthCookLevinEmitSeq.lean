import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoopProg3

/-!
# Cook–Levin M2 emitter — the sequencing layer

The run-composition spine: `seqMachine M1 M2` is one `ComposableMachine` that runs `M1` to its halt,
resets the head, and runs `M2` — the mechanism by which the family emitters chain into the grand
transducer.

**The composition theorem is unconditional.**  The model's `step` is idempotent at halt states
(`step_of_halted`), which kills the classical no-early-halt side condition: if `M1` reaches its halt
phase before its stated clock, it *freezes* there, so its stated run theorem still names the first-halt
configuration (`run_stable`); the composed machine hands off at the true first halt time `tm ≤ t1`,
runs `M2` to its halt, and then freezes through the surplus `t1 - tm` steps — landing on `M2`'s final
configuration at **exactly** the budgeted clock `t1 + 1 + t2`.  So `seq_run` needs only the two run
theorems and the two halt flags — precisely what every emitter brick's top theorem provides.

The handoff resets the head to `0` (`init`-form), so any two engines whose tape interfaces meet — the
first's output tape is the second's input tape — compose.  Demonstrations: `progSeq_run` chains two
program emitters (the straight-line engine's layout is its own interface, so chaining is unconditional),
and `progSeq3_run` chains three by iterating the binary theorem — no associativity lemma needed, the
composed machine's top theorem is itself `seq_run`-shaped.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice

/-! ## The sequential composition -/

/-- **Sequential composition**: run `M1`; at its halt, reset the head and enter `M2`.  The composite
halts exactly at `M2`'s halts. -/
def seqMachine (M1 M2 : Machine) : Machine where
  State := M1.State ⊕ M2.State
  fin := letI := M1.fin; letI := M2.fin; inferInstance
  dec := letI := M1.dec; letI := M2.dec; inferInstance
  start := Sum.inl M1.start
  halt := fun s => match s with
    | .inl _ => false
    | .inr s2 => M2.halt s2
  δ := fun s b => match s with
    | .inl s1 =>
      if M1.halt s1 then (Sum.inr M2.start, none, 3)
      else (Sum.inl (M1.δ s1 b).1, (M1.δ s1 b).2.1, (M1.δ s1 b).2.2)
    | .inr s2 => (Sum.inr (M2.δ s2 b).1, (M2.δ s2 b).2.1, (M2.δ s2 b).2.2)
  accept := fun s => match s with
    | .inl _ => false
    | .inr s2 => M2.accept s2

/-- Embed an `M1`-configuration. -/
def inlCfg (M1 M2 : Machine) (c : Cfg M1) : Cfg (seqMachine M1 M2) := ⟨.inl c.st, c.hd, c.tp⟩

/-- Embed an `M2`-configuration. -/
def inrCfg (M1 M2 : Machine) (c : Cfg M2) : Cfg (seqMachine M1 M2) := ⟨.inr c.st, c.hd, c.tp⟩

theorem seq_halt_inl (M1 M2 : Machine) (s : M1.State) :
    (seqMachine M1 M2).halt (Sum.inl s) = false := rfl

theorem seq_halt_inr (M1 M2 : Machine) (s : M2.State) :
    (seqMachine M1 M2).halt (Sum.inr s) = M2.halt s := rfl

theorem init_seq (M1 M2 : Machine) (x : List Bool) :
    init (seqMachine M1 M2) x = inlCfg M1 M2 (init M1 x) := rfl

/-! ### The three step laws -/

theorem seq_delta_inl (M1 M2 : Machine) (s1 : M1.State) (b : Bool)
    (h : M1.halt s1 = false) :
    (seqMachine M1 M2).δ (Sum.inl s1) b
      = (Sum.inl (M1.δ s1 b).1, (M1.δ s1 b).2.1, (M1.δ s1 b).2.2) := by
  show (if M1.halt s1 then _ else _) = _
  rw [h]
  simp

theorem seq_delta_inl_halt (M1 M2 : Machine) (s1 : M1.State) (b : Bool)
    (h : M1.halt s1 = true) :
    (seqMachine M1 M2).δ (Sum.inl s1) b = (Sum.inr M2.start, none, 3) := by
  show (if M1.halt s1 then _ else _) = _
  rw [h]
  simp

theorem seq_delta_inr (M1 M2 : Machine) (s2 : M2.State) (b : Bool) :
    (seqMachine M1 M2).δ (Sum.inr s2) b
      = (Sum.inr (M2.δ s2 b).1, (M2.δ s2 b).2.1, (M2.δ s2 b).2.2) := rfl

/-- Left phase, not yet halted: the composite simulates `M1`. -/
theorem step_seq_inl (M1 M2 : Machine) (c : Cfg M1) (h : M1.halt c.st = false) :
    step (seqMachine M1 M2) (inlCfg M1 M2 c) = inlCfg M1 M2 (step M1 c) := by
  unfold step
  rw [show (inlCfg M1 M2 c).st = Sum.inl c.st from rfl, seq_halt_inl, h]
  simp only [Bool.false_eq_true, if_false]
  rw [show (inlCfg M1 M2 c).tp = c.tp from rfl, show (inlCfg M1 M2 c).hd = c.hd from rfl,
    seq_delta_inl M1 M2 c.st _ h]
  rfl

/-- Left phase, halted: the handoff — head reset, `M2`'s start. -/
theorem step_seq_handoff (M1 M2 : Machine) (c : Cfg M1) (h : M1.halt c.st = true) :
    step (seqMachine M1 M2) (inlCfg M1 M2 c) = ⟨Sum.inr M2.start, 0, c.tp⟩ := by
  unfold step
  rw [show (inlCfg M1 M2 c).st = Sum.inl c.st from rfl, seq_halt_inl]
  simp only [Bool.false_eq_true, if_false]
  rw [show (inlCfg M1 M2 c).tp = c.tp from rfl, show (inlCfg M1 M2 c).hd = c.hd from rfl,
    seq_delta_inl_halt M1 M2 c.st _ h]
  rfl

/-- Right phase: the composite simulates `M2` unconditionally (the freeze conditions agree). -/
theorem step_seq_inr (M1 M2 : Machine) (c : Cfg M2) :
    step (seqMachine M1 M2) (inrCfg M1 M2 c) = inrCfg M1 M2 (step M2 c) := by
  by_cases h : M2.halt c.st = true
  · have h2 : (seqMachine M1 M2).halt (inrCfg M1 M2 c).st = true := by
      rw [show (inrCfg M1 M2 c).st = Sum.inr c.st from rfl, seq_halt_inr]
      exact h
    rw [step_of_halted M2 h, step_of_halted (seqMachine M1 M2) h2]
  · have h' : M2.halt c.st = false := by simpa using h
    unfold step
    rw [show (inrCfg M1 M2 c).st = Sum.inr c.st from rfl, seq_halt_inr, h']
    simp only [Bool.false_eq_true, if_false]
    rw [show (inrCfg M1 M2 c).tp = c.tp from rfl, show (inrCfg M1 M2 c).hd = c.hd from rfl,
      seq_delta_inr]
    rfl

/-! ### The two simulations -/

/-- The right simulation, unconditional. -/
theorem run_seq_inr (M1 M2 : Machine) (c : Cfg M2) (t : ℕ) :
    run (seqMachine M1 M2) t (inrCfg M1 M2 c) = inrCfg M1 M2 (run M2 t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_seq_inr, ← run_succ]

/-- The left simulation, below the first halt. -/
theorem run_seq_inl (M1 M2 : Machine) (c : Cfg M1) (t : ℕ)
    (h : ∀ t', t' < t → M1.halt (run M1 t' c).st = false) :
    run (seqMachine M1 M2) t (inlCfg M1 M2 c) = inlCfg M1 M2 (run M1 t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun t' ht' => h t' (by omega)),
      step_seq_inl M1 M2 _ (h t (by omega)), ← run_succ]

/-! ## THE COMPOSITION THEOREM -/

/-- **Sequential runs compose, unconditionally.**  Given `M1`'s run theorem (halting, tape `T0 ↦ T1`)
and `M2`'s (halting, tape `T1 ↦ T2`), the composite reaches `M2`'s final configuration — halted — at
**exactly** the clock `t1 + 1 + t2`.  No side condition about early halting: the freeze semantics
absorbs any slack between `M1`'s first halt and its stated clock. -/
theorem seq_run (M1 M2 : Machine) (T0 T1 T2 : List Bool) (t1 t2 : ℕ)
    (s1f : M1.State) (p1 : ℕ) (s2f : M2.State) (p2 : ℕ)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1f, p1, T1⟩) (hh1 : M1.halt s1f = true)
    (h2 : run M2 t2 (init M2 T1) = ⟨s2f, p2, T2⟩) (hh2 : M2.halt s2f = true) :
    run (seqMachine M1 M2) (t1 + 1 + t2) (init (seqMachine M1 M2) T0)
      = ⟨Sum.inr s2f, p2, T2⟩ := by
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
  have hs1 := run_seq_inl M1 M2 (init M1 T0) (Nat.find hex) hno
  rw [hfrozen] at hs1
  have hstep := step_seq_handoff M1 M2 (⟨s1f, p1, T1⟩ : Cfg M1) hh1
  have hs2 := run_seq_inr M1 M2 (init M2 T1) t2
  rw [h2] at hs2
  have hfin : (seqMachine M1 M2).halt
      (inrCfg M1 M2 (⟨s2f, p2, T2⟩ : Cfg M2)).st = true := by
    rw [show (inrCfg M1 M2 (⟨s2f, p2, T2⟩ : Cfg M2)).st = Sum.inr s2f from rfl,
      seq_halt_inr]
    exact hh2
  rw [show t1 + 1 + t2 = Nat.find hex + (1 + (t2 + (t1 - Nat.find hex))) from by omega,
    run_add, init_seq, hs1, run_add,
    show run (seqMachine M1 M2) 1 (inlCfg M1 M2 (⟨s1f, p1, T1⟩ : Cfg M1))
      = ⟨Sum.inr M2.start, 0, T1⟩ from by rw [run_succ, run_zero]; exact hstep,
    show (⟨Sum.inr M2.start, 0, T1⟩ : Cfg (seqMachine M1 M2))
      = inrCfg M1 M2 (init M2 T1) from rfl,
    run_add, hs2, run_of_halted (seqMachine M1 M2) hfin]
  rfl

/-- The composite's final state is halted (so composed runs chain again). -/
theorem seq_halt_final (M1 M2 : Machine) (s2f : M2.State) (hh2 : M2.halt s2f = true) :
    (seqMachine M1 M2).halt (Sum.inr s2f) = true := by
  rw [seq_halt_inr]; exact hh2

/-! ## Demonstrations: chaining the straight-line engine

The program emitter's tape interface is its own layout (`unaryD v ++ encodeD out`, the counter
preserved), so program emitters chain unconditionally — two runs, then three by iterating the binary
theorem on its own output. -/

/-- **Two chained program emitters**: one machine, both programs' denotations appended in order. -/
theorem progSeq_run (p1 p2 : List (Option Bool)) (v : ℕ) (out : List Bool) :
    run (seqMachine (progMachine p1) (progMachine p2))
      (pgClock p1 v out.length + 1 + pgClock p2 v (out ++ progOut p1 v).length)
      (init (seqMachine (progMachine p1) (progMachine p2)) (unaryD v ++ encodeD out))
      = ⟨Sum.inr (30, ⟨p2.length, Nat.lt_succ_self _⟩, false), 0,
          unaryD v ++ encodeD ((out ++ progOut p1 v) ++ progOut p2 v)⟩ :=
  seq_run (progMachine p1) (progMachine p2) _ _ _ _ _ _ _ _ _
    (prog_run p1 v out) rfl (prog_run p2 v (out ++ progOut p1 v)) rfl

/-- **Three chained program emitters** — the binary theorem iterates on its own output; no
associativity bookkeeping. -/
theorem progSeq3_run (p1 p2 p3 : List (Option Bool)) (v : ℕ) (out : List Bool) :
    run (seqMachine (seqMachine (progMachine p1) (progMachine p2)) (progMachine p3))
      ((pgClock p1 v out.length + 1 + pgClock p2 v (out ++ progOut p1 v).length) + 1
        + pgClock p3 v ((out ++ progOut p1 v) ++ progOut p2 v).length)
      (init (seqMachine (seqMachine (progMachine p1) (progMachine p2)) (progMachine p3))
        (unaryD v ++ encodeD out))
      = ⟨Sum.inr (30, ⟨p3.length, Nat.lt_succ_self _⟩, false), 0,
          unaryD v ++ encodeD ((((out ++ progOut p1 v) ++ progOut p2 v)
            ++ progOut p3 v))⟩ :=
  seq_run (seqMachine (progMachine p1) (progMachine p2)) (progMachine p3) _ _ _ _ _ _ _ _ _
    (progSeq_run p1 p2 v out)
    (seq_halt_final (progMachine p1) (progMachine p2) _ rfl)
    (prog_run p3 v ((out ++ progOut p1 v) ++ progOut p2 v)) rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq