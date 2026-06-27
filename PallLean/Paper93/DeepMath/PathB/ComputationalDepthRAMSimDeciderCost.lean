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

set_option maxHeartbeats 2000000 in
set_option linter.unusedTactic false in
/-- **Intra-tick value bound — the crux of the copy-branch (simulator-loop) value bound.**  This is where the
loop differs from the init/complement phases: the values *grow* (the code pointer `C` and `sim_acc` `A` climb),
and the body has `addI` at `pc 25`/`pc 28` operating on `A`/`C`.  The generic accumulator bound `≤ V` does not
suffice (`addI` would give `≤ V+1`); one must know the *exact* accumulator at each `pc`.

For one **`INC`** tick (fetched opcode `0`) from the loop top `pc = 14`, with the tick-top values bounded
(`clock = N+1`, pointer `C`, `sim_acc = A`, all `≤ V`, and `A+1, C+1, N+1 ≤ V` giving headroom for the two
`addI`s), every one of the `17` intra-tick states stays value-bounded by `V`.  Proved by computing each of the
`17` states explicitly (`interval_cases j` + `simp [run, …]`) and bounding its accumulator and memory — the
per-`pc` accumulator is thereby exact, discharging the `addI` growth.

Composing this over the `bound` ticks (via `simLoop_one` for the tick boundaries) and the run decomposition
`k = 17·t + j` gives the full copy-branch value bound; that assembly is the remaining mechanical step. -/
theorem tick_intra_valueBounded (m : Mem) (acc0 V N C A : ℕ)
    (h0 : m 0 = N + 1) (h1 : m 1 = 1) (h2 : m 2 = C) (h3 : m 3 = A) (hacc0 : acc0 ≤ V)
    (hCcode : m C = 0)
    (hbV : ∀ x, m x ≤ V) (hN : N + 1 ≤ V) (hA : A + 1 ≤ V) (hC : C + 1 ≤ V) :
    ∀ j, j ≤ 17 → ValueBounded (run simDecider ⟨m, acc0, 14, false⟩ j) V := by
  intro j hj
  interval_cases j <;>
    refine ⟨by simp [run, step, simDecider, List.getD, h0, h1, h2, h3, hCcode] <;> omega,
            by intro x
               simp [run, step, simDecider, List.getD, Mem.set, h0, h1, h2, h3, hCcode]
               (try split_ifs) <;> first | omega | exact hbV _⟩

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **The full simulator-loop value bound** (all-`INC` code).  Composing `tick_intra_valueBounded` (intra-tick)
over the `N` ticks via `simLoop_one` (tick step) and the run decomposition `j = 17·t + i`: from the loop top
`pc = 14` with clock `= N`, pointer `= base ≥ 5`, all-`INC` code on the range, and the bounds `base + N ≤ V`,
`sim_acc + N ≤ V` (the pointer and accumulator climb to `base + N` / `sim_acc + N`), **every** state of the
`17·N + 3`-step loop run stays value-bounded by `V`.  Induction on the tick count `N`. -/
theorem loop_valueBounded (N : ℕ) :
    ∀ (m : Mem) (acc V base : ℕ), m 0 = N → m 1 = 1 → m 2 = base → 5 ≤ base →
      (∀ i, i < N → m (base + i) = 0) → (∀ x, m x ≤ V) → acc ≤ V →
      base + N ≤ V → m 3 + N ≤ V →
      ∀ j, j ≤ 17 * N + 3 → ValueBounded (run simDecider ⟨m, acc, 14, false⟩ j) V := by
  induction N with
  | zero =>
    intro m acc V base h0 _ _ _ _ hbV hacc _ _ j hj
    interval_cases j <;>
      refine ⟨by simp [run, step, simDecider, List.getD, h0] <;> omega,
              by intro x
                 simp [run, step, simDecider, List.getD, Mem.set, h0]
                 first | omega | exact hacc | exact hbV _⟩
  | succ N ih =>
    intro m acc V base h0 h1 h2 hb5 hcode hbV hacc hbase hsim j hj
    have hc0 : m base = 0 := by have := hcode 0 (by omega); simpa using this
    by_cases hj17 : j ≤ 17
    · exact tick_intra_valueBounded m acc V N base (m 3) h0 h1 h2 rfl hacc
        hc0 hbV (by omega) (by omega) (by omega) j hj17
    · have hone : run simDecider ⟨m, acc, 14, false⟩ 17
          = ⟨(((m.set 4 1).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N, N, 14, false⟩ :=
        simLoop_one m acc N h0 h1 (by rw [h2]; exact hc0)
      set M' : Mem := (((m.set 4 1).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N with hM'
      have hsplit : run simDecider ⟨m, acc, 14, false⟩ j
          = run simDecider ⟨M', N, 14, false⟩ (j - 17) := by
        have hh : run simDecider ⟨m, acc, 14, false⟩ (17 + (j - 17))
            = run simDecider ⟨M', N, 14, false⟩ (j - 17) := by rw [run_add, hone]
        rwa [show 17 + (j - 17) = j from by omega] at hh
      rw [hsplit]
      have hM0 : M' 0 = N := by simp [hM']
      have hM1 : M' 1 = 1 := by simp [hM', h1]
      have hM2 : M' 2 = base + 1 := by simp [hM', h2]
      have hM3 : M' 3 = m 3 + 1 := by simp [hM']
      have hINC : ∀ i, i < N → M' (base + 1 + i) = 0 := by
        intro i hi
        have hc := hcode (i + 1) (by omega)
        have he : M' (base + 1 + i) = m (base + 1 + i) := by
          rw [hM', Mem.set_get_ne _ 0 _ _ (by omega), Mem.set_get_ne _ 2 _ _ (by omega),
            Mem.set_get_ne _ 3 _ _ (by omega), Mem.set_get_ne _ 4 _ _ (by omega)]
        rw [he, show base + 1 + i = base + (i + 1) from by ring]; exact hc
      have hMbV : ∀ x, M' x ≤ V := by
        intro x
        simp only [hM', Mem.set]
        split_ifs <;> first | omega | exact hbV _
      exact ih M' N V (base + 1) hM0 hM1 hM2 (by omega) hINC hMbV (by omega)
        (by omega) (by rw [hM3]; omega) (j - 17) (by omega)

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.run_succ_right
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.init_valueBounded
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.complement_valueBounded
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_complement_cost
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.tick_intra_valueBounded
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.loop_valueBounded
