import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMLoop
import Mathlib.Tactic

/-!
# RAM memo DP — the DP body fused into the loop, verified (PROVED) — step 2, brick 4

Bricks 1–3 gave the pieces: addressable cell access (`cellCopy`), indexed table read/write
(`tableGet`/`tableSet`), and a verified clocked loop (`countLoop`).  This brick **fuses them**: a loop whose
body, each iteration, **memoises a running DP value into the table** through a walking pointer and advances the
DP state — and we prove that after the loop the table genuinely holds the memoised values, the real content of
"the memo table".

`dpLoop` walks a pointer `p = mem[2]` forward across the table, writing the running DP accumulator `v = mem[3]`
into `mem[p]` each step and incrementing `v`, while a counter `mem[0]` clocks the loop:

```
  0: loadI 0   1: jzI 13   2: loadI 3   3: storeIndI 2   4: addI 1   5: storeI 3   6: loadI 2
  7: addI 1    8: storeI 2  9: loadI 0  10: subI 1       11: storeI 0 12: jmpI 0   13: haltI
```

Layout: `mem[0]=counter`, `mem[1]=1`, `mem[2]=pointer` (table base, `≥ 4` so the table is disjoint from the
scratch cells), `mem[3]=DP accumulator`.

  `dpNext` / `dpNext_*` — the exact memory effect of one iteration, with its cell projections.
  `dpLoop_one` — one live iteration is exactly `13` steps and realises `dpNext`.
  `dpLoop_correct` — from counter `N`, after **exactly `13·N + 3` steps** the machine is halted with
        `counter = 0`, `pointer = base + N`, `accumulator = v₀ + N`, **and the table is filled**:
        `mem[base + j] = v₀ + j` for every `j < N` (the memoised DP values), while cells below the table are
        untouched.  Proved by induction on `N` — a genuine array loop invariant.
  `dpLoop_runCost_le` — the run costs `≤ (13·N + 3)·(3W + 1)` bits under a maintained width bound; the step
        count is *proved exact*, so no hidden unit-cost step counting.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This is the memo DP itself, running as a real RAM program.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The DP loop: walk pointer `mem[2]` across the table, writing accumulator `mem[3]` and advancing it, while
counter `mem[0]` clocks the iterations. -/
def dpLoop : List Instr :=
  [ Instr.loadI 0      -- 0:  acc := counter
  , Instr.jzI 13       -- 1:  if counter = 0 goto halt
  , Instr.loadI 3      -- 2:  acc := v
  , Instr.storeIndI 2  -- 3:  mem[p] := v        (memoise current DP value)
  , Instr.addI 1       -- 4:  acc := v + 1
  , Instr.storeI 3     -- 5:  v := v + 1         (DP transition)
  , Instr.loadI 2      -- 6:  acc := p
  , Instr.addI 1       -- 7:  acc := p + 1
  , Instr.storeI 2     -- 8:  p := p + 1         (advance pointer)
  , Instr.loadI 0      -- 9:  acc := counter
  , Instr.subI 1       -- 10: acc := counter - 1
  , Instr.storeI 0     -- 11: counter := counter - 1
  , Instr.jmpI 0       -- 12: loop back to top
  , Instr.haltI ]      -- 13: stop

/-- The exact memory after one live iteration: `mem[p] := v`, `v := v+1`, `p := p+1`, `counter := N`
(`p = m 2`, `v = m 3`, written in execution order). -/
def dpNext (m : Mem) (N : ℕ) : Mem :=
  (((m.set (m 2) (m 3)).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N

@[simp] theorem dpNext_0 (m : Mem) (N : ℕ) : dpNext m N 0 = N := by simp [dpNext]
@[simp] theorem dpNext_2 (m : Mem) (N : ℕ) : dpNext m N 2 = m 2 + 1 := by simp [dpNext]
@[simp] theorem dpNext_3 (m : Mem) (N : ℕ) : dpNext m N 3 = m 3 + 1 := by simp [dpNext]

theorem dpNext_1 (m : Mem) (N : ℕ) (hb : 4 ≤ m 2) : dpNext m N 1 = m 1 := by
  have : (1 : ℕ) ≠ m 2 := by omega
  simp [dpNext, this]

theorem dpNext_base (m : Mem) (N : ℕ) (hb : 4 ≤ m 2) : dpNext m N (m 2) = m 3 := by
  have h0 : m 2 ≠ 0 := by omega
  have h2 : m 2 ≠ 2 := by omega
  have h3 : m 2 ≠ 3 := by omega
  simp [dpNext, h0, h2, h3]

theorem dpNext_other (m : Mem) (N a : ℕ) (h0 : a ≠ 0) (h2 : a ≠ 2) (h3 : a ≠ 3) (hm : a ≠ m 2) :
    dpNext m N a = m a := by simp [dpNext, h0, h2, h3, hm]

/-- **One live iteration is exactly `13` steps** and realises the `dpNext` memory effect: it writes the DP
accumulator into the table cell at the pointer, advances the pointer and the accumulator, and decrements the
counter. -/
theorem dpLoop_one (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hb : 4 ≤ m 2) :
    run dpLoop ⟨m, acc, 0, false⟩ 13 = ⟨dpNext m N, N, 0, false⟩ := by
  have e0 : (0 : ℕ) ≠ m 2 := by omega
  have e1 : (1 : ℕ) ≠ m 2 := by omega
  have e2 : (2 : ℕ) ≠ m 2 := by omega
  show step dpLoop (step dpLoop (step dpLoop (step dpLoop (step dpLoop (step dpLoop (step dpLoop
        (step dpLoop (step dpLoop (step dpLoop (step dpLoop (step dpLoop (step dpLoop
        ⟨m, acc, 0, false⟩)))))))))))) = _
  simp [step, dpLoop, List.getD, h0, h1, e0, e1, e2, dpNext]

/-- **The memo DP runs exactly `N` times and fills the table.**  From counter `mem[0] = N`, pointer
`mem[2] = base ≥ 4`, accumulator `mem[3] = v₀`, after exactly `13·N + 3` steps the machine is halted, the
counter is `0`, the pointer is `base + N`, the accumulator is `v₀ + N`, and the table holds the memoised values
`mem[base + j] = v₀ + j` for all `j < N`, with cells below the table untouched. -/
theorem dpLoop_correct (N : ℕ) :
    ∀ (m : Mem) (acc : ℕ), m 0 = N → m 1 = 1 → 4 ≤ m 2 →
      let S := run dpLoop ⟨m, acc, 0, false⟩ (13 * N + 3)
      S.halted = true ∧ S.mem 0 = 0 ∧ S.mem 2 = m 2 + N ∧ S.mem 3 = m 3 + N
        ∧ (∀ j, j < N → S.mem (m 2 + j) = m 3 + j)
        ∧ (∀ a, 4 ≤ a → a < m 2 → S.mem a = m a) := by
  induction N with
  | zero =>
    intro m acc h0 _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, step, dpLoop, List.getD, h0]
  | succ N ih =>
    intro m acc h0 h1 hb
    have hsplit : 13 * (N + 1) + 3 = 13 + (13 * N + 3) := by ring
    have hone : run dpLoop ⟨m, acc, 0, false⟩ 13 = ⟨dpNext m N, N, 0, false⟩ :=
      dpLoop_one m acc N h0 h1 hb
    have hm0 : dpNext m N 0 = N := dpNext_0 m N
    have hm1 : dpNext m N 1 = 1 := by rw [dpNext_1 m N hb]; exact h1
    have hm2 : 4 ≤ dpNext m N 2 := by rw [dpNext_2 m N]; omega
    have key := ih (dpNext m N) N hm0 hm1 hm2
    have hSeq : run dpLoop ⟨m, acc, 0, false⟩ (13 * (N + 1) + 3)
        = run dpLoop ⟨dpNext m N, N, 0, false⟩ (13 * N + 3) := by
      rw [hsplit, run_add, hone]
    simp only [hSeq]
    obtain ⟨kh, k0, k2, k3, ktab, kpre⟩ := key
    refine ⟨kh, k0, ?_, ?_, ?_, ?_⟩
    · rw [k2, dpNext_2 m N]; ring
    · rw [k3, dpNext_3 m N]; ring
    · intro j hj
      obtain _ | i := j
      · simp only [Nat.add_zero]
        rw [kpre (m 2) (by omega) (by rw [dpNext_2 m N]; omega), dpNext_base m N hb]
      · have hi : i < N := by omega
        have htab := ktab i hi
        rw [dpNext_2 m N, dpNext_3 m N] at htab
        have harg : m 2 + (i + 1) = m 2 + 1 + i := by ring
        rw [harg, htab]; ring
    · intro a ha4 haN
      rw [kpre a ha4 (by rw [dpNext_2 m N]; omega)]
      exact dpNext_other m N a (by omega) (by omega) (by omega) (by omega)

/-- **Honest poly bit-cost of the memo DP.**  When every reached state stays `W`-width-bounded (the
program-specific invariant — same interface as `runCost_width_le`), the exact `13·N + 3`-step run costs
`≤ (13·N + 3)·(3W + 1)` bits.  The step count is *proved exact* (`dpLoop_correct`), so there is no hidden
unit-cost step counting. -/
theorem dpLoop_runCost_le (m : Mem) (acc N W : ℕ)
    (h : ∀ k, k < 13 * N + 3 → WidthBounded dpLoop (run dpLoop ⟨m, acc, 0, false⟩ k) W) :
    runCost dpLoop ⟨m, acc, 0, false⟩ (13 * N + 3) ≤ (13 * N + 3) * (3 * W + 1) :=
  runCost_width_le dpLoop ⟨m, acc, 0, false⟩ (13 * N + 3) W h

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_one
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_runCost_le
