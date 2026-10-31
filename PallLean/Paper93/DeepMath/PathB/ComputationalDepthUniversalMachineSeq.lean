import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Head-move construction, brick 6: position-preserving sequential composition (`seq`)

The marked-head primitives (bricks 1–5) each halt in their own control state; assembling `uStepOnTape`
means *chaining* them — seek to the marked head, then act at that position.  The corpus already has a
sequential composition `comp`, but its switch step **resets the head to 0** (a `reset` move, for the
reduction-closure use case).  That reset destroys a sought position before the next operation can use
it: `comp (scanToTrue) (shiftRight)` would seek the marker, then jump back to 0 and shift the wrong
cell.

This brick builds the sequencer the assembly actually needs: `seq Mf Mg`, identical to `comp` except the
switch is a `stay` move — `Mg` starts exactly where `Mf` left the head.  So a sought position feeds the
next operation intact.

## What is proved

* **`seq`** — `Mf.State ⊕ Mg.State`; run `Mf`; when it halts, one control step switches to `Mg.start`
  with the head and tape **unchanged** (the only difference from `comp`).
* **`seq_step_inl` / `seq_step_switch` / `seq_step_inr`** — the three local steps; the switch lands on
  `⟨Mg.start, cf.hd, cf.tp⟩` (head preserved, vs `comp`'s `⟨Mg.start, 0, cf.tp⟩`).
* **`seq_phase1`** — up to `Mf`'s first halt, `seq` mirrors `Mf`.
* **`seq_phase2`** — from the switched config, `seq` mirrors `Mg` run from the preserved position.
* **`seq_switch_preserves_head`** — the payoff: at the switch, `seq` hands `Mg` the head `Mf` ended on,
  not `0`.
* **`seq_runs`** — the full composition: `seq` runs `Mf` to its halt, then `Mg` from `Mf`'s ending
  head/tape.

## Honest scope

`seq` is the position-preserving sequencer — the piece that lets `scanToTrue`'s found marker feed
`shiftRight`, and generally lets the marked-head primitives chain into a simulated step.  With bricks
1–5 (all the operations) it makes the remaining `uStepOnTape` assembly a matter of wiring proven
machines, plus the rule lookup; then the lazy-delay diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineSeq

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Position-preserving sequential composition.**  Like `comp`, but the `Mf → Mg` switch keeps the
head where `Mf` left it (a `stay` move, `2`) instead of resetting to `0` (`comp`'s `reset`, `3`). -/
def seq (Mf Mg : Machine) : Machine where
  State := Mf.State ⊕ Mg.State
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl Mf.start
  halt := fun s => match s with | .inl _ => false | .inr sg => Mg.halt sg
  δ := fun s b => match s with
    | .inl sf => if Mf.halt sf then (Sum.inr Mg.start, none, (2 : Move))
                 else let tr := Mf.δ sf b; (Sum.inl tr.1, tr.2.1, tr.2.2)
    | .inr sg => let tr := Mg.δ sg b; (Sum.inr tr.1, tr.2.1, tr.2.2)
  accept := fun s => match s with | .inl _ => false | .inr sg => Mg.accept sg

/-- Embed an `Mf` config into the sequence (first phase). -/
def seqEmbedL (Mf Mg : Machine) (c : Cfg Mf) : Cfg (seq Mf Mg) := ⟨Sum.inl c.st, c.hd, c.tp⟩

/-- Embed an `Mg` config into the sequence (second phase). -/
def seqEmbedR (Mf Mg : Machine) (c : Cfg Mg) : Cfg (seq Mf Mg) := ⟨Sum.inr c.st, c.hd, c.tp⟩

/-- Phase-1 step: while `Mf` has not halted, `seq` mirrors `Mf`. -/
theorem seq_step_inl (Mf Mg : Machine) (cf : Cfg Mf) (h : Mf.halt cf.st = false) :
    step (seq Mf Mg) (seqEmbedL Mf Mg cf) = seqEmbedL Mf Mg (step Mf cf) := by
  simp only [step, seq, seqEmbedL, h, Bool.false_eq_true, ↓reduceIte]

/-- **The switch step (head preserved).**  When `Mf` has halted, one `seq` step moves to `Mg`'s start
keeping the head (`cf.hd`) and tape — the sole difference from `comp`, which resets the head to `0`. -/
theorem seq_step_switch (Mf Mg : Machine) (cf : Cfg Mf) (h : Mf.halt cf.st = true) :
    step (seq Mf Mg) (seqEmbedL Mf Mg cf) = seqEmbedR Mf Mg ⟨Mg.start, cf.hd, cf.tp⟩ := by
  simp only [step, seq, seqEmbedL, seqEmbedR, h, Bool.false_eq_true, ↓reduceIte, moveHead]
  rfl

/-- Phase-2 step: `seq` mirrors `Mg`. -/
theorem seq_step_inr (Mf Mg : Machine) (cg : Cfg Mg) :
    step (seq Mf Mg) (seqEmbedR Mf Mg cg) = seqEmbedR Mf Mg (step Mg cg) := by
  simp only [step, seq, seqEmbedR]
  by_cases h : Mg.halt cg.st = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

/-- **Phase 1 (proved).**  For `t` up to `Mf`'s first halt, `seq` simulates `Mf`. -/
theorem seq_phase1 (Mf Mg : Machine) (x : List Bool) (t : ℕ)
    (hmin : ∀ s < t, Mf.halt (run Mf s (init Mf x)).st = false) :
    run (seq Mf Mg) t (init (seq Mf Mg) x) = seqEmbedL Mf Mg (run Mf t (init Mf x)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun s hs => hmin s (Nat.lt_succ_of_lt hs))]
    rw [seq_step_inl Mf Mg _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-- **Phase 2 (proved).**  From a phase-2 embedded config, `seq` simulates `Mg` run from that (preserved)
position. -/
theorem seq_phase2 (Mf Mg : Machine) (cg0 : Cfg Mg) (s : ℕ) (base : Cfg (seq Mf Mg))
    (hsw : base = seqEmbedR Mf Mg cg0) :
    run (seq Mf Mg) s base = seqEmbedR Mf Mg (run Mg s cg0) := by
  subst hsw
  induction s with
  | zero => rfl
  | succ s ih => rw [run_succ, ih, seq_step_inr, ← run_succ]

/-- **The payoff (proved): the switch preserves the head.**  When `Mf` halts at time `t` with head `H`
and tape `T`, `seq` switches to `Mg` at head `H` — not `0`.  This is exactly what `comp` cannot do, and
what lets a sought position feed the next operation. -/
theorem seq_switch_preserves_head (Mf Mg : Machine) (x : List Bool) (t : ℕ)
    (hmin : ∀ s < t, Mf.halt (run Mf s (init Mf x)).st = false)
    (hhalt : Mf.halt (run Mf t (init Mf x)).st = true) :
    run (seq Mf Mg) (t + 1) (init (seq Mf Mg) x)
      = seqEmbedR Mf Mg ⟨Mg.start, (run Mf t (init Mf x)).hd, (run Mf t (init Mf x)).tp⟩ := by
  rw [run_succ, seq_phase1 Mf Mg x t hmin, seq_step_switch Mf Mg _ hhalt]

/-- **The full composition (proved).**  `seq` runs `Mf` to its first halt, then runs `Mg` from `Mf`'s
ending head and tape — a genuine sequential composition that carries position across the switch. -/
theorem seq_runs (Mf Mg : Machine) (x : List Bool) (t s : ℕ)
    (hmin : ∀ s' < t, Mf.halt (run Mf s' (init Mf x)).st = false)
    (hhalt : Mf.halt (run Mf t (init Mf x)).st = true) :
    run (seq Mf Mg) (t + 1 + s) (init (seq Mf Mg) x)
      = seqEmbedR Mf Mg
          (run Mg s ⟨Mg.start, (run Mf t (init Mf x)).hd, (run Mf t (init Mf x)).tp⟩) := by
  rw [run_add, seq_switch_preserves_head Mf Mg x t hmin hhalt]
  exact seq_phase2 Mf Mg _ s _ rfl

end PallLean.Paper93.DeepMath.PathB.UniversalMachineSeq

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeq.seq_switch_preserves_head
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeq.seq_runs
