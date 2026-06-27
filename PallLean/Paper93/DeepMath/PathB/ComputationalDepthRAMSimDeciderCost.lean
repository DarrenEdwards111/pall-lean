import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMValueBound
import Mathlib.Tactic

/-!
# Discharging the `simDecider` value bound — the init phase (PROVED) — step 3 (continued)

`simDecider_runCost_le` reduces the integrated decider's bit-cost to a value bound on its reachable states.
This file begins discharging that value bound *unconditionally* (given a bounded input), starting with the
shared **init phase** (`pc 0..8`): the eight setup steps that load the clock, constant, accumulator, and code
pointer and read the mode.  These instructions are jump-free and growth-free (only `loadI`/`storeI`/`constI`
with literals `0,1`), so the value bound is maintained step by step — `step_mem_le` handles memory
unconditionally and `step_acc_le`'s growth side conditions are vacuous here.

  `run_succ_right` — `run prog s (k+1) = step prog (run prog s k)` (step on the right), from `run_add`.
  `init_valueBounded` — for a `V`-bounded input, every state of the first `9` steps of `simDecider` stays
        value-bounded by `V`, with `pc = k` and not halted.  The shared foundation for both branches' costs.

This is the unconditional start of the value-bound discharge; the `jzI` dispatch and the two branches (the
complement tail and the simulator loop) extend it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- **Step on the right**: `run prog s (k+1) = step prog (run prog s k)`.  (`run` unfolds step-first; this is
the step-last form, from machine-level additivity.) -/
theorem run_succ_right (prog : List Instr) (s : State) (k : ℕ) :
    run prog s (k + 1) = step prog (run prog s k) := by
  rw [run_add]; rfl

set_option maxHeartbeats 1000000 in
/-- **The init phase keeps the value bound.**  For an input value-bounded by `V` (`acc ≤ V`, every cell `≤ V`,
`1 ≤ V`), each of the first `9` states of `simDecider` is value-bounded by `V`, sits at `pc = k`, and is not
halted.  The eight init instructions are jump-free and non-growing, so the bound is preserved unconditionally
(`step_mem_le` for memory; the growth side conditions of `step_acc_le` are vacuous as no `addI`/`loadIndI`/
large-`constI` runs). -/
theorem init_valueBounded (m : Mem) (acc V : ℕ)
    (hin : ∀ x, m x ≤ V) (hacc : acc ≤ V) (h1 : 1 ≤ V) :
    ∀ k, k ≤ 9 →
      ValueBounded (run simDecider ⟨m, acc, 0, false⟩ k) V
        ∧ (run simDecider ⟨m, acc, 0, false⟩ k).pc = k
        ∧ (run simDecider ⟨m, acc, 0, false⟩ k).halted = false := by
  intro k
  induction k with
  | zero => intro _; exact ⟨⟨hacc, hin⟩, rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hvb, hpc, hhalt⟩ := ih (by omega)
    have hk8 : k ≤ 8 := by omega
    rw [run_succ_right]
    interval_cases k <;>
      refine ⟨step_valueBounded simDecider _ V hvb
          (by intro v h; rw [hpc] at h; simp [simDecider, List.getD] at h <;> omega)
          (by intro a h; rw [hpc] at h; simp [simDecider, List.getD] at h)
          (by intro a h; rw [hpc] at h; simp [simDecider, List.getD] at h), ?_, ?_⟩ <;>
      simp_all [step, simDecider, List.getD]

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.run_succ_right
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.init_valueBounded
