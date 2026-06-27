import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDecode
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — copy branch invokes the clock, verified (PROVED) — step 2, brick 2

Brick 1 (`decodeDispatch`) decoded the input and dispatched to a copy or complement branch, but the copy branch
just echoed.  Here the copy branch **invokes a real clock loop**: it runs a bounded countdown of length
`bound` (decoded from the input) — the lazy "simulate `M_code` for `bound` steps" budget — and only then halts.
This is the "clock to a bound" piece of the diagonal decider, now genuinely wired behind the dispatch.

The new engineering content is a backward-jump loop sitting at an **absolute pc offset** (12) inside the larger
program, entered by the dispatch jump; we prove its loop invariant directly (mirroring `countLoop_correct` at
the offset) and compose the phases with `run_add`.

Layout: `mem[10]=bound  mem[11]=mode  mem[12]=inp`; `mem[0]=counter mem[1]=1 mem[2]=tally mem[3]=result`.

```
  0..5:  init — counter:=bound, one:=1, tally:=0
  6: loadI 11  7: jzI 12                 -- dispatch (mode=0 → clock loop at 12)
  8: constI 1  9: subI 12  10: storeI 3  11: haltI      -- complement: result := 1 - inp
  12: loadI 0  13: jzI 20  14: subI 1  15: storeI 0     -- clock loop: counter--
  16: loadI 2  17: addI 1  18: storeI 2  19: jmpI 12    --            tally++, loop
  20: loadI 2  21: storeI 3  22: haltI                  -- done: result := tally
```

  `clockLoop_one` — one clock iteration is exactly `8` steps (counter--, tally++), pc back to `12`.
  `clockLoop_correct` — from the loop top with `counter = N`, after exactly `8·N + 5` steps the machine halts
        with `counter = 0`, `tally = result = (initial tally) + N`: the clock ran exactly `N` times.
  `clockedDecider_copy` — `mode = 0`: the decider runs exactly `8·bound + 13` steps and halts with
        `result = bound` — the copy branch clocked the full `bound`-step budget (the step count scales with the
        decoded bound: a genuine "clock to a bound").
  `clockedDecider_complement` — `mode ≠ 0`: halts after exactly `12` steps with `result = 1 - inp` (flip).
  `clockedDecider_diagonal` — on a complement input with `inp ∈ {0,1}`, the result differs from `inp`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This wires the clock behind the dispatch; a real universal
simulator inside the clocked budget, and the final diagonal wrap, are later bricks.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The decoder whose copy branch invokes a bounded clock loop. -/
def clockedDecider : List Instr :=
  [ Instr.loadI 10, Instr.storeI 0       -- 0,1:  counter := bound
  , Instr.constI 1, Instr.storeI 1       -- 2,3:  one := 1
  , Instr.constI 0, Instr.storeI 2       -- 4,5:  tally := 0
  , Instr.loadI 11, Instr.jzI 12         -- 6,7:  dispatch on mode
  , Instr.constI 1, Instr.subI 12, Instr.storeI 3, Instr.haltI  -- 8..11: complement → 1 - inp
  , Instr.loadI 0, Instr.jzI 20          -- 12,13: clock loop top / exit test
  , Instr.subI 1, Instr.storeI 0         -- 14,15: counter--
  , Instr.loadI 2, Instr.addI 1, Instr.storeI 2, Instr.jmpI 12  -- 16..19: tally++, loop
  , Instr.loadI 2, Instr.storeI 3, Instr.haltI ]  -- 20,21,22: done → result := tally

/-- **One clock iteration is exactly `8` steps**: decrement the counter, increment the tally, `pc` back to the
loop top `12`. -/
theorem clockLoop_one (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) :
    run clockedDecider ⟨m, acc, 12, false⟩ 8
      = ⟨(m.set 0 N).set 2 (m 2 + 1), m 2 + 1, 12, false⟩ := by
  show step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
    (step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
    (⟨m, acc, 12, false⟩)))))))) = _
  simp [step, clockedDecider, List.getD, Mem.set, h0, h1]

/-- **The clock runs exactly `N` times.**  From the loop top with `counter = N` and `one = 1`, after exactly
`8·N + 5` steps the machine halts with `counter = 0` and `tally = result = (initial tally) + N`. -/
theorem clockLoop_correct (N : ℕ) :
    ∀ (m : Mem) (acc : ℕ), m 0 = N → m 1 = 1 →
      let S := run clockedDecider ⟨m, acc, 12, false⟩ (8 * N + 5)
      S.halted = true ∧ S.mem 0 = 0 ∧ S.mem 2 = m 2 + N ∧ S.mem 3 = m 2 + N := by
  induction N with
  | zero =>
    intro m acc h0 _
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, step, clockedDecider, List.getD, h0]
  | succ N ih =>
    intro m acc h0 h1
    have hsplit : 8 * (N + 1) + 5 = 8 + (8 * N + 5) := by ring
    have hone : run clockedDecider ⟨m, acc, 12, false⟩ 8
        = ⟨(m.set 0 N).set 2 (m 2 + 1), m 2 + 1, 12, false⟩ := clockLoop_one m acc N h0 h1
    set M' : Mem := (m.set 0 N).set 2 (m 2 + 1) with hM'
    have hM'0 : M' 0 = N := by simp [hM']
    have hM'1 : M' 1 = 1 := by simp [hM', h1]
    have hM'2 : M' 2 = m 2 + 1 := by simp [hM']
    have key := ih M' (m 2 + 1) hM'0 hM'1
    have hSeq : run clockedDecider ⟨m, acc, 12, false⟩ (8 * (N + 1) + 5)
        = run clockedDecider ⟨M', m 2 + 1, 12, false⟩ (8 * N + 5) := by
      rw [hsplit, run_add, hone]
    simp only [hSeq]
    obtain ⟨kh, k0, k2, k3⟩ := key
    refine ⟨kh, k0, ?_, ?_⟩
    · rw [k2, hM'2]; ring
    · rw [k3, hM'2]; ring

/-- The exact state after the `8`-step init+dispatch on a **copy** input (`mode = 0`): registers initialised,
control at the clock-loop top `pc = 12`. -/
theorem copy_prefix (m : Mem) (acc : ℕ) (hmode : m 11 = 0) :
    run clockedDecider ⟨m, acc, 0, false⟩ 8
      = ⟨((m.set 0 (m 10)).set 1 1).set 2 0, 0, 12, false⟩ := by
  show step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
    (step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
    (⟨m, acc, 0, false⟩)))))))) = _
  simp [step, clockedDecider, List.getD, hmode]

/-- The exact state after the `8`-step init+dispatch on a **complement** input (`mode ≠ 0`): control falls
through to the complement branch at `pc = 8`. -/
theorem complement_prefix (m : Mem) (acc : ℕ) (hmode : m 11 ≠ 0) :
    run clockedDecider ⟨m, acc, 0, false⟩ 8
      = ⟨((m.set 0 (m 10)).set 1 1).set 2 0, m 11, 8, false⟩ := by
  show step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
    (step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
    (⟨m, acc, 0, false⟩)))))))) = _
  simp [step, clockedDecider, List.getD, hmode]

/-- **Copy branch invokes the clock**: when `mode = 0`, the decider runs exactly `8·bound + 13` steps and halts
with `result = bound` — it clocked the full `bound`-step budget.  The step count scales with the decoded
`bound`: a genuine clock-to-a-bound behind the dispatch. -/
theorem clockedDecider_copy (m : Mem) (acc : ℕ) (hmode : m 11 = 0) :
    (run clockedDecider ⟨m, acc, 0, false⟩ (8 * m 10 + 13)).halted = true
      ∧ (run clockedDecider ⟨m, acc, 0, false⟩ (8 * m 10 + 13)).mem 3 = m 10 := by
  have hrw : run clockedDecider ⟨m, acc, 0, false⟩ (8 * m 10 + 13)
      = run clockedDecider ⟨((m.set 0 (m 10)).set 1 1).set 2 0, 0, 12, false⟩ (8 * m 10 + 5) := by
    rw [show 8 * m 10 + 13 = 8 + (8 * m 10 + 5) from by ring, run_add, copy_prefix m acc hmode]
  rw [hrw]
  have hpre0 : (((m.set 0 (m 10)).set 1 1).set 2 0) 0 = m 10 := by simp
  have hpre1 : (((m.set 0 (m 10)).set 1 1).set 2 0) 1 = 1 := by simp
  have key := clockLoop_correct (m 10) (((m.set 0 (m 10)).set 1 1).set 2 0) 0 hpre0 hpre1
  obtain ⟨kh, _, _, k3⟩ := key
  refine ⟨kh, ?_⟩
  rw [k3]; simp

/-- **Complement branch**: when `mode ≠ 0`, the decider halts after exactly `12` steps with `result = 1 - inp`
— it flips the input bit (the boundary branch), bypassing the clock. -/
theorem clockedDecider_complement (m : Mem) (acc : ℕ) (hmode : m 11 ≠ 0) :
    (run clockedDecider ⟨m, acc, 0, false⟩ 12).halted = true
      ∧ (run clockedDecider ⟨m, acc, 0, false⟩ 12).mem 3 = 1 - m 12 := by
  have hrw : run clockedDecider ⟨m, acc, 0, false⟩ 12
      = run clockedDecider ⟨((m.set 0 (m 10)).set 1 1).set 2 0, m 11, 8, false⟩ 4 := by
    rw [show (12 : ℕ) = 8 + 4 from rfl, run_add, complement_prefix m acc hmode]
  rw [hrw]
  constructor
  · show (step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
      (⟨((m.set 0 (m 10)).set 1 1).set 2 0, m 11, 8, false⟩))))).halted = true
    simp [step, clockedDecider, List.getD]
  · show (step clockedDecider (step clockedDecider (step clockedDecider (step clockedDecider
      (⟨((m.set 0 (m 10)).set 1 1).set 2 0, m 11, 8, false⟩))))).mem 3 = 1 - m 12
    simp [step, clockedDecider, List.getD]

/-- **The diagonal flip** survives the clocked decider: on a complement input with `inp ∈ {0,1}`, the result
differs from `inp`. -/
theorem clockedDecider_diagonal (m : Mem) (acc : ℕ) (hmode : m 11 ≠ 0) (hbit : m 12 ≤ 1) :
    (run clockedDecider ⟨m, acc, 0, false⟩ 12).mem 3 ≠ m 12 := by
  have h := (clockedDecider_complement m acc hmode).2
  rw [h]; omega

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.clockLoop_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.clockedDecider_copy
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.clockedDecider_complement
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.clockedDecider_diagonal
