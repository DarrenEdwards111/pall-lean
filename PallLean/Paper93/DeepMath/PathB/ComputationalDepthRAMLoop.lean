import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMTable
import Mathlib.Tactic

/-!
# RAM memo DP — a verified clocked loop (PROVED) — step 2, brick 3

Bricks 1–2 gave the straight-line table operations (`cellCopy`, `tableGet`/`tableSet`).  The memo DP
*iterates* them over the rank range, and the lazy-diagonal decider must **clock to a bound** — both need a
real loop: a backward jump (`jmpI`) with a counter test (`jzI`) that runs an *exactly* known number of
iterations and then halts.  This brick supplies the genuine control-flow primitive and proves it correct.

`countLoop` is a concrete ISA program with a real backward jump that, from a counter `mem[0] = N`, runs `N`
iterations — each decrements the counter (`mem[0]`) and increments a tally (`mem[2]`) — and then halts:

```
  0: loadI 0   1: jzI 8   2: subI 1   3: storeI 0
  4: loadI 2   5: addI 1  6: storeI 2 7: jmpI 0   8: haltI
```

  `run_add` — running `a + b` steps = running `a` then `b` (machine-level additivity of `run`).
  `countLoop_one` — one live iteration (`mem[0] = N+1`) is exactly `8` steps and decrements the counter,
                    increments the tally, and returns `pc` to `0`.
  `countLoop_correct` — from `mem[0] = N`, after **exactly** `8·N + 3` steps the machine is halted with
                    `mem[0] = 0` and `mem[2] = (initial mem[2]) + N`: the loop ran exactly `N` times.
  `countLoop_runCost_le` — that run costs `≤ (8·N + 3)·(3W + 1)` in bits when the reached states stay
                    `W`-width-bounded (the program-specific invariant, same interface as `runCost_width_le`):
                    an honest poly bit-cost for the clock — **no hidden unit-cost step counting**.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This is the loop the memo DP and the diagonal clock iterate.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- **Machine-level additivity of `run`**: `a + b` steps = `a` steps then `b` steps. -/
theorem run_add (prog : List Instr) (s : State) (a b : ℕ) :
    run prog s (a + b) = run prog (run prog s a) b := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    have hcomm : a + 1 + b = a + b + 1 := by ring
    rw [hcomm, run_succ, run_succ, ih]

/-- A clocked countdown loop with a **real backward jump**: counter in `mem[0]`, constant `1` in `mem[1]`,
tally in `mem[2]`.  Each iteration decrements the counter and increments the tally; when the counter reaches
`0` it halts. -/
def countLoop : List Instr :=
  [ Instr.loadI 0    -- 0: acc := count
  , Instr.jzI 8      -- 1: if count = 0 goto halt
  , Instr.subI 1     -- 2: acc := count - 1
  , Instr.storeI 0   -- 3: count := count - 1
  , Instr.loadI 2    -- 4: acc := tally
  , Instr.addI 1     -- 5: acc := tally + 1
  , Instr.storeI 2   -- 6: tally := tally + 1
  , Instr.jmpI 0     -- 7: loop back to top
  , Instr.haltI ]    -- 8: stop

/-- **One live iteration is exactly `8` steps** and transforms the state by decrementing the counter (`mem[0]`)
and incrementing the tally (`mem[2]`), returning `pc` to the top. -/
theorem countLoop_one (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) :
    run countLoop ⟨m, acc, 0, false⟩ 8
      = ⟨(m.set 0 N).set 2 (m 2 + 1), m 2 + 1, 0, false⟩ := by
  show step countLoop (step countLoop (step countLoop (step countLoop (step countLoop
        (step countLoop (step countLoop (step countLoop ⟨m, acc, 0, false⟩))))))) = _
  simp [step, countLoop, List.getD, Mem.set, h0, h1]

/-- **The loop runs exactly `N` times.**  From a counter `mem[0] = N`, after exactly `8·N + 3` steps the
machine is halted, the counter is `0`, and the tally `mem[2]` has been incremented exactly `N` times. -/
theorem countLoop_correct (N : ℕ) :
    ∀ (m : Mem) (acc : ℕ), m 0 = N → m 1 = 1 →
      let s := run countLoop ⟨m, acc, 0, false⟩ (8 * N + 3)
      s.halted = true ∧ s.mem 0 = 0 ∧ s.mem 2 = m 2 + N := by
  induction N with
  | zero =>
    intro m acc h0 _
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [run, step, countLoop, List.getD, h0]
  | succ N ih =>
    intro m acc h0 h1
    -- split 8·(N+1)+3 = 8 + (8·N+3); run one iteration, then apply the IH
    have hsplit : 8 * (N + 1) + 3 = 8 + (8 * N + 3) := by ring
    set M' : Mem := (m.set 0 N).set 2 (m 2 + 1) with hM'
    have hstep : run countLoop ⟨m, acc, 0, false⟩ 8 = ⟨M', m 2 + 1, 0, false⟩ :=
      countLoop_one m acc N h0 h1
    have hM'0 : M' 0 = N := by simp [hM']
    have hM'1 : M' 1 = 1 := by simp [hM', Mem.set, h1]
    have hM'2 : M' 2 = m 2 + 1 := by simp [hM']
    have key := ih M' (m 2 + 1) hM'0 hM'1
    have hreassoc : run countLoop ⟨m, acc, 0, false⟩ (8 * (N + 1) + 3)
        = run countLoop ⟨M', m 2 + 1, 0, false⟩ (8 * N + 3) := by
      rw [hsplit, run_add, hstep]
    simp only [hreassoc]
    refine ⟨key.1, key.2.1, ?_⟩
    rw [key.2.2, hM'2]; ring

/-- **Honest poly bit-cost of the clock.**  When every reached state stays `W`-width-bounded (the
program-specific invariant — same interface as `runCost_width_le`), the exact `8·N + 3`-step run costs
`≤ (8·N + 3)·(3W + 1)` in bits.  The step count is *proved exact* (`countLoop_correct`), so there is no hidden
unit-cost step counting. -/
theorem countLoop_runCost_le (m : Mem) (acc N W : ℕ)
    (h : ∀ k, k < 8 * N + 3 → WidthBounded countLoop (run countLoop ⟨m, acc, 0, false⟩ k) W) :
    runCost countLoop ⟨m, acc, 0, false⟩ (8 * N + 3) ≤ (8 * N + 3) * (3 * W + 1) :=
  runCost_width_le countLoop ⟨m, acc, 0, false⟩ (8 * N + 3) W h

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.run_add
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.countLoop_one
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.countLoop_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.countLoop_runCost_le
