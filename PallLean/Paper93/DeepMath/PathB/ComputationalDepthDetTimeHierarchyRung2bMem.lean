import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDetTimeHierarchyRung2b

/-!
# Time hierarchy, rung 2b (memory-image half): simulated memory read/write with cost

Rung 2b's interpreter half (`…Rung2bInterp`) realised fetch + opcode dispatch on an accumulator ISA.  The full RAM
`uStepFn` (rung 2a) also has instructions that read and write the simulated machine's **memory** (`loadI`, `storeI`,
and their indirect variants).  This file realises that missing mechanism: a **simulated memory image** — the simulated
cell `a` lives at real address `MEMBASE + a` — accessed by **computed-address indirect addressing** (`loadIndI` /
`storeIndI` on a scratch cell holding `MEMBASE + a`), with an exact per-macro-step cost and linear clocking overhead.

  `memStoreInterp` / `memStoreInterp_step` / `memStoreInterp_iterate` — a store loop `simMem[idx] := simAcc; idx += 1`:
        the write goes to the memory image at the *computed* address `MEMBASE + idx` via `storeIndI`, exact cost `9`,
        `k` steps in exactly `9k`.
  `memLoadInterp` / `memLoadInterp_step` / `memLoadInterp_iterate` — a load loop `simAcc := simMem[idx]; idx += 1`:
        the read comes from the memory image at `MEMBASE + idx` via `loadIndI`, exact cost `9`, `k` steps in `9k`.
  `MemAligned` — the aligned invariant, with `8 ≤ mem[MEMBASE-cell]` so the image region (`≥ MEMBASE`) is disjoint from
        the interpreter's control cells (`0..8`); the write/read of `MEMBASE + idx` therefore never corrupts control
        state, which the preservation proofs discharge by `omega`.

With rung 2b's fetch + dispatch and this file's memory image, all three core interpreter mechanisms — indirect fetch,
opcode dispatch, and simulated-memory read/write — are now genuine `List Instr` with proved exact cost.

## Honest scope

These are genuine `List Instr` interpreters realising the **simulated-memory** mechanism (computed-address indirect
load/store into a memory image) with proved exact cost and linear overhead on the real RAM `run`.  Each still simulates
a single-purpose loop, not yet the full ten-opcode `uStepFn`: the remaining work is the mechanical assembly of one
interpreter that decodes `(op, arg)` (rung 2a's codec), dispatches ten ways (rung 2b's dispatch pattern), runs the
matching handler — accumulator ops, control ops, and these memory ops — with every handler **padded to one uniform
cost**, and whose macro-step equals `uStepFn`.  Then `run_macro_iterate` gives `run uProg s (k·cost) = k` faithful
`uStepFn` steps, feeding rung 1's `UniversalRAMRealizesDiagonal` to close the *deterministic* hierarchy; the
*nondeterministic* lift (lazy diagonalisation) remains.  Nothing here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-- Aligned interpreter state for the memory-image loops.  Cells `0..8` are control/scratch; the simulated memory image
lives at real addresses `≥ MEMBASE = mem[6]`, and `8 ≤ MEMBASE` keeps the image disjoint from control cells. -/
def MemAligned (s : State) : Prop := s.halted = false ∧ s.pc = 0 ∧ s.mem 2 = 1 ∧ 8 ≤ s.mem 6

/-! ### Store into the simulated memory image (computed-address `storeIndI`) -/

/-- A store loop: `simMem[idx] := simAcc; idx += 1`.  Cell `1` = `simAcc`, cell `2` = constant `1`, cell `5` = `idx`,
cell `6` = `MEMBASE`, cell `7` = scratch address.  The address `MEMBASE + idx` is computed into cell `7`, then
`storeIndI 7` writes `simAcc` to real address `MEMBASE + idx` (the image cell for `simMem[idx]`) — the write comes
**last**, so no read follows it. -/
def memStoreInterp : List Instr :=
  [ .loadI 6, .addI 5, .storeI 7, .loadI 5, .addI 2, .storeI 5, .loadI 1, .storeIndI 7, .jmpI 0 ]

/-- The macro-step `memStoreInterp` realises: write `simAcc` to the image cell `MEMBASE + idx`, then `idx += 1`. -/
def memStoreMstep (s : State) : State :=
  { mem := ((s.mem.set 7 (s.mem 6 + s.mem 5)).set 5 (s.mem 5 + 1)).set (s.mem 6 + s.mem 5) (s.mem 1),
    acc := s.mem 1, pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost, memory write (proved)**: from an aligned state, `memStoreInterp` writes the simulated
memory image and advances in exactly `9` real steps. -/
theorem memStoreInterp_step (s : State) (h : MemAligned s) : run memStoreInterp s 9 = memStoreMstep s := by
  obtain ⟨hh, hpc, hc, _⟩ := h
  simp [run, step, memStoreInterp, hh, hpc, hc, memStoreMstep]

/-- The store macro-step preserves the aligned invariant (the image write at `MEMBASE + idx ≥ 8` misses control cells
`2` and `6`, discharged by `omega`). -/
theorem memStoreMstep_pres (s : State) (h : MemAligned s) : MemAligned (memStoreMstep s) := by
  obtain ⟨hh, hpc, hc, hb⟩ := h
  refine ⟨hh, rfl, ?_, ?_⟩
  · simp only [memStoreMstep, Mem.set]; simp [show (2 : ℕ) ≠ s.mem 6 + s.mem 5 by omega, hc]
  · simp only [memStoreMstep, Mem.set]; simp [show (6 : ℕ) ≠ s.mem 6 + s.mem 5 by omega, hb]

/-- **Linear clocking overhead, memory write (proved)**: `k` store macro-steps run in *exactly* `9k` real steps. -/
theorem memStoreInterp_iterate (k : ℕ) (s : State) (h : MemAligned s) :
    run memStoreInterp s (k * 9) = memStoreMstep^[k] s :=
  run_macro_iterate memStoreInterp memStoreMstep 9 MemAligned memStoreMstep_pres memStoreInterp_step k s h

/-! ### Load from the simulated memory image (computed-address `loadIndI`) -/

/-- A load loop: `simAcc := simMem[idx]; idx += 1`.  The address `MEMBASE + idx` is computed into cell `7`, then
`loadIndI 7` reads the image cell for `simMem[idx]` into `simAcc`. -/
def memLoadInterp : List Instr :=
  [ .loadI 6, .addI 5, .storeI 7, .loadIndI 7, .storeI 1, .loadI 5, .addI 2, .storeI 5, .jmpI 0 ]

/-- The macro-step `memLoadInterp` realises: read the image cell `MEMBASE + idx` into `simAcc`, then `idx += 1`. -/
def memLoadMstep (s : State) : State :=
  { mem := ((s.mem.set 7 (s.mem 6 + s.mem 5)).set 1 (s.mem (s.mem 6 + s.mem 5))).set 5 (s.mem 5 + 1),
    acc := s.mem 5 + 1, pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost, memory read (proved)**: from an aligned state, `memLoadInterp` reads the simulated
memory image and advances in exactly `9` real steps (the image read at `MEMBASE + idx ≥ 8` misses the scratch cell `7`,
discharged by `omega`). -/
theorem memLoadInterp_step (s : State) (h : MemAligned s) : run memLoadInterp s 9 = memLoadMstep s := by
  obtain ⟨hh, hpc, hc, hb⟩ := h
  simp [run, step, memLoadInterp, hh, hpc, hc, memLoadMstep, show s.mem 6 + s.mem 5 ≠ 7 by omega]

/-- The load macro-step preserves the aligned invariant (it writes only control cells `1`, `5`, `7`). -/
theorem memLoadMstep_pres (s : State) (h : MemAligned s) : MemAligned (memLoadMstep s) := by
  obtain ⟨hh, hpc, hc, hb⟩ := h
  exact ⟨hh, rfl, by simp [memLoadMstep, hc], by simp [memLoadMstep, hb]⟩

/-- **Linear clocking overhead, memory read (proved)**: `k` load macro-steps run in *exactly* `9k` real steps. -/
theorem memLoadInterp_iterate (k : ℕ) (s : State) (h : MemAligned s) :
    run memLoadInterp s (k * 9) = memLoadMstep^[k] s :=
  run_macro_iterate memLoadInterp memLoadMstep 9 MemAligned memLoadMstep_pres memLoadInterp_step k s h

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.memStoreInterp_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.memStoreInterp_iterate
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.memLoadInterp_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.memLoadInterp_iterate
