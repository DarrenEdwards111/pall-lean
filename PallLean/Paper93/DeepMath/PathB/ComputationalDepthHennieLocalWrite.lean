import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHenniePeak

/-!
# Local write-free excursions via a stop-before-write machine

`HenniePeak` needs a frontier that remains blank for an entire halting run.  A moving tape frontier
does not satisfy that hypothesis in the original machine, because a later step may write beyond it.

This file constructs the correct local reduction.  `stopBeforeWrite M` simulates `M` while its
transition has no write.  When `M` would next write, the auxiliary machine instead enters a fresh
halt state without changing the tape or head.  Its tape is therefore globally constant, making the
blank-frontier hypothesis valid.  The resulting `head_lt_at_next_write` bounds the original head at
the end of any write-free phase.

This is a local machine lemma, not a SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.HennieLocalWrite

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- A simulator that stops immediately before the next write transition. -/
def stopBeforeWrite (M : Machine) : Machine where
  State := M.State ⊕ Unit
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl M.start
  halt := fun s => match s with
    | .inl q => M.halt q
    | .inr _ => true
  δ := fun s b => match s with
    | .inl q =>
        let tr := M.δ q b
        match tr.2.1 with
        | none => (Sum.inl tr.1, none, tr.2.2)
        | some _ => (Sum.inr (), none, (2 : Move))
    | .inr _ => (Sum.inr (), none, (2 : Move))
  accept := fun s => match s with
    | .inl q => M.accept q
    | .inr _ => false

/-- Embed an original configuration in the running phase. -/
def embed (c : Cfg M) : Cfg (stopBeforeWrite M) := ⟨Sum.inl c.st, c.hd, c.tp⟩

/-- The stopped configuration retains the pre-write head and tape. -/
def stopped (c : Cfg M) : Cfg (stopBeforeWrite M) := ⟨Sum.inr (), c.hd, c.tp⟩

@[simp] theorem halt_embed (c : Cfg M) :
    (stopBeforeWrite M).halt (embed c).st = M.halt c.st := rfl

@[simp] theorem halt_stopped (c : Cfg M) :
    (stopBeforeWrite M).halt (stopped c).st = true := rfl

/-- A no-write transition is simulated exactly. -/
theorem step_embed_of_none (c : Cfg M) (hhalt : M.halt c.st = false)
    (hnone : (M.δ c.st (c.tp.getD c.hd false)).2.1 = none) :
    step (stopBeforeWrite M) (embed c) = embed (step M c) := by
  unfold step embed
  simp only [stopBeforeWrite, hhalt, Bool.false_eq_true, ↓reduceIte]
  rw [hnone]

/-- A write transition is replaced by a pure transition to the stopped state. -/
theorem step_embed_of_some (c : Cfg M) (hhalt : M.halt c.st = false) {w : Bool}
    (hsome : (M.δ c.st (c.tp.getD c.hd false)).2.1 = some w) :
    step (stopBeforeWrite M) (embed c) = stopped c := by
  unfold step embed stopped
  simp only [stopBeforeWrite, hhalt, Bool.false_eq_true, ↓reduceIte]
  rw [hsome]
  rfl

/-- The auxiliary machine never changes its tape. -/
theorem step_tp_eq (c : Cfg (stopBeforeWrite M)) :
    (step (stopBeforeWrite M) c).tp = c.tp := by
  rcases c with ⟨q, h, tp⟩
  rcases q with q | u
  · by_cases hh : M.halt q = true
    · simp [step, stopBeforeWrite, hh]
    · simp only [Bool.not_eq_true] at hh
      rcases hw : (M.δ q (tp.getD h false)).2.1 with _ | w
      · unfold step
        simp only [stopBeforeWrite, hh, Bool.false_eq_true, ↓reduceIte]
        rw [hw]
      · unfold step
        simp only [stopBeforeWrite, hh, Bool.false_eq_true, ↓reduceIte]
        rw [hw]
  · simp [step, stopBeforeWrite]

/-- Consequently its tape is constant for every run length. -/
theorem run_tp_eq (c : Cfg (stopBeforeWrite M)) (t : ℕ) :
    (run (stopBeforeWrite M) t c).tp = c.tp := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, step_tp_eq, ih]

/-- The original run has no write transition before time `t`. -/
def WriteFreeBefore (M : Machine) (c : Cfg M) (t : ℕ) : Prop :=
  ∀ j, j < t →
    M.halt (run M j c).st = false ∧
      (M.δ (run M j c).st
        ((run M j c).tp.getD (run M j c).hd false)).2.1 = none

/-- Simulation through a write-free prefix. -/
theorem run_eq_embed_of_writeFree (c : Cfg M) {t : ℕ}
    (hfree : WriteFreeBefore M c t) :
    run (stopBeforeWrite M) t (embed c) = embed (run M t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun j hj => hfree j (by omega)),
        step_embed_of_none _ (hfree t (by omega)).1 (hfree t (by omega)).2,
        ← run_succ]

/-- At the following write, the auxiliary run enters its halt state with the original pre-write
head and tape. -/
theorem run_succ_eq_stopped (c : Cfg M) {t : ℕ}
    (hfree : WriteFreeBefore M c t)
    (hhalt : M.halt (run M t c).st = false) {w : Bool}
    (hwrite : (M.δ (run M t c).st
      ((run M t c).tp.getD (run M t c).hd false)).2.1 = some w) :
    run (stopBeforeWrite M) (t + 1) (embed c) = stopped (run M t c) := by
  rw [run_succ, run_eq_embed_of_writeFree c hfree,
    step_embed_of_some _ hhalt hwrite]

/-- **Local blank-excursion head bound.**  If `M` performs no writes for `t` steps and would write
at step `t`, its pre-write head is within the initial tape frontier plus the state count of the
stop-before-write simulator.  This is a sound moving-frontier primitive: later writes by `M` are
irrelevant because the auxiliary machine has already halted. -/
theorem head_lt_at_next_write (c : Cfg M) {t : ℕ}
    (hfree : WriteFreeBefore M c t)
    (hstart : c.hd < c.tp.length + 1)
    (hhalt : M.halt (run M t c).st = false) {w : Bool}
    (hwrite : (M.δ (run M t c).st
      ((run M t c).tp.getD (run M t c).hd false)).2.1 = some w) :
    (run M t c).hd < c.tp.length + 1 + Fintype.card (stopBeforeWrite M).State := by
  let A := stopBeforeWrite M
  have hAhalt : A.halt (run A (t + 1) (embed c)).st = true := by
    rw [run_succ_eq_stopped c hfree hhalt hwrite]
    rfl
  have hAfirst : ∀ j, j < t + 1 → A.halt (run A j (embed c)).st = false := by
    intro j hj
    have hjt : j ≤ t := by omega
    have hsim : run A j (embed c) = embed (run M j c) := by
      apply run_eq_embed_of_writeFree
      intro k hk
      exact hfree k (lt_of_lt_of_le hk hjt)
    rw [hsim, halt_embed]
    rcases lt_or_eq_of_le hjt with hjlt | rfl
    · exact (hfree j hjlt).1
    · exact hhalt
  have hblank : ∀ s, c.tp.length + 1 ≤ (run A s (embed c)).hd →
      (run A s (embed c)).tp.getD (run A s (embed c)).hd false = false := by
    intro s hs
    have htp : (run A s (embed c)).tp = c.tp := by
      rw [run_tp_eq]
      rfl
    rw [htp]
    have hlen : c.tp.length ≤ (run A s (embed c)).hd := by omega
    simp [List.getD, List.getElem?_eq_none hlen]
  have hpeak := HenniePeak.head_lt_of_blank (M := A) (embed c)
    (c.tp.length + 1) (t + 1) (by omega) hstart hAhalt hAfirst hblank t (by omega)
  rw [run_eq_embed_of_writeFree c hfree] at hpeak
  exact hpeak

end PallLean.Paper93.DeepMath.PathB.HennieLocalWrite
