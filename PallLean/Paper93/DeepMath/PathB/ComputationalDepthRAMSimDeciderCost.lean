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

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

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

/-- The accumulator at the dispatch point `pc = 9` is the mode `mem[11]` (loaded by the `loadI 11` at `pc 8`).
A direct `9`-step computation. -/
theorem acc_at_dispatch (m : Mem) (acc : ℕ) :
    (run simDecider ⟨m, acc, 0, false⟩ 9).acc = m 11 := by
  show (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (step simDecider (step simDecider (step simDecider (step simDecider
    (⟨m, acc, 0, false⟩)))))))))).acc = m 11
  simp [step, simDecider, List.getD]

set_option maxHeartbeats 1000000 in
/-- **The complement branch keeps the value bound (the whole `14` steps).**  For a `V`-bounded input with a
nonzero mode (`m 11 ≠ 0`), every state of the first `14` steps of `simDecider` stays value-bounded by `V`, at
`pc = k`, not halted.  Extends `init_valueBounded` through the `jzI` dispatch at `pc 9` (which, since
`acc = mode ≠ 0`, falls through to the complement branch `pc 10` — discharged from `acc_at_dispatch` and
`hmode`) and the complement tail (`pc 10..13`: `constI 1`, `subI 12`, `storeI 3`, `haltI`), all non-growing. -/
theorem complement_valueBounded (m : Mem) (acc V : ℕ)
    (hin : ∀ x, m x ≤ V) (hacc : acc ≤ V) (h1 : 1 ≤ V) (hmode : m 11 ≠ 0) :
    ∀ k, k ≤ 13 →
      ValueBounded (run simDecider ⟨m, acc, 0, false⟩ k) V
        ∧ (run simDecider ⟨m, acc, 0, false⟩ k).pc = k
        ∧ (run simDecider ⟨m, acc, 0, false⟩ k).halted = false := by
  have hd := acc_at_dispatch m acc
  intro k
  induction k with
  | zero => intro _; exact ⟨⟨hacc, hin⟩, rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hvb, hpc, hhalt⟩ := ih (by omega)
    have hk12 : k ≤ 12 := by omega
    rw [run_succ_right]
    interval_cases k <;>
      refine ⟨step_valueBounded simDecider _ V hvb
          (by intro v h; rw [hpc] at h; simp [simDecider, List.getD] at h <;> omega)
          (by intro a h; rw [hpc] at h; simp [simDecider, List.getD] at h)
          (by intro a h; rw [hpc] at h; simp [simDecider, List.getD] at h), ?_, ?_⟩ <;>
      simp_all [step, simDecider, List.getD]

/-- **The complement branch runs in polynomial bit-cost — unconditionally** (given a `V`-bounded input,
`bitlen V ≤ W`, `W ≥ 6`, and a nonzero mode).  Its `14` steps cost `≤ 14·(3W + 1)` bits, with **no width or
value hypothesis** left: the value bound is discharged by `complement_valueBounded`.  A complete, hypothesis-free
bit-cost for a real branch of the integrated decider. -/
theorem simDecider_complement_cost (m : Mem) (acc V W : ℕ)
    (hin : ∀ x, m x ≤ V) (hacc : acc ≤ V) (h1 : 1 ≤ V) (hmode : m 11 ≠ 0)
    (hV : bitlen V ≤ W) (hW : 6 ≤ W) :
    runCost simDecider ⟨m, acc, 0, false⟩ 14 ≤ 14 * (3 * W + 1) :=
  simDecider_runCost_le m acc 14 W V hV hW
    (fun k hk => (complement_valueBounded m acc V hin hacc h1 hmode k (by omega)).1)

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.run_succ_right
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.init_valueBounded
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.complement_valueBounded
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_complement_cost
