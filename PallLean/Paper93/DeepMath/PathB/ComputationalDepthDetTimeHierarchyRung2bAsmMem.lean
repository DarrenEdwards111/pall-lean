import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDetTimeHierarchyRung2b

/-!
# Time hierarchy, rung 2b (assembly + memory): a memory-image handler folded into the dispatch

The assembly backbone (`…Rung2bAsm`) decoded `(op, arg)` and dispatched to register/immediate handlers.  The one
integration not yet shown is a **simulated-memory handler inside the unified dispatch** — a dispatch branch that writes
the memory image (`…Rung2bMem` proved memory access only in standalone loops).  This file does exactly that: one
interpreter that decodes `(op, arg)`, dispatches, and on one branch performs a **computed-address memory write** into
the simulated image, with a uniform per-macro-step cost feeding the linear-overhead backbone.

  `asmMem` — a real `List Instr` interpreter: decode `op = mem[pp]`, `arg = mem[pp+1]`, advance `pp += 2`, compute the
        image address `MEMBASE + arg`, then dispatch on `op` (`jzI`): `op = 0` ↦ `sacc := arg` (immediate), `op ≠ 0` ↦
        `simMem[arg] := sacc` (**memory write via `storeIndI`**); both branches run in the uniform cost `19`.
  `asmMem_step` — **PROVED**: from an aligned state, one macro-step runs in exactly `19` real steps on either branch —
        the immediate branch and the **memory-writing** branch have the same cost.
  `asmMemMstep_pres` / `asmMem_iterate` — **PROVED**: the macro-step preserves the aligned invariant (the image write at
        `MEMBASE + arg ≥ 8` misses the control cells `2`, `3`, `5`, `6`, discharged by `omega`), and `k` macro-steps run
        in exactly `19k` real steps.

This closes the last *distinct* integration of the assembly: a memory-image handler and an immediate handler under one
`(op, arg)` decode and dispatch, at one uniform cost.

## Honest scope

Every distinct mechanism of the full interpreter is now proved as a `List Instr` program and shown to compose:
two-field `(op, arg)` decode, opcode dispatch, immediate handlers, a **memory-image handler inside the dispatch**
(this file), uniform-cost padding, and linear overhead.  What remains for the full ten-opcode `uStepFn` is *purely*
adding the other handlers (double-indirect `loadIndI`/`storeIndI`, `addI`/`subI` over the image, control
`jzI`/`jmpI`/`haltI` on the simulated `pc`) to the same dispatch by the identical pattern, each padded to one uniform
cost, and proving the assembled macro-step equals `uStepFn` — mechanical repetition with no new mechanism.  Then
`run_macro_iterate` gives `run uProg s (k·cost) = k` faithful `uStepFn` steps, feeding rung 1's
`UniversalRAMRealizesDiagonal` to close the *deterministic* hierarchy; the *nondeterministic* lift (lazy
diagonalisation) is the genuinely-different remaining difficulty.  Nothing here is `NondetTimeHierarchy`,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-- The assembled interpreter with a **memory handler in the dispatch**.  Cells: `1` = `sacc`, `2` = const `1`,
`3` = const `2`, `5` = program pointer `pp`, `6` = `MEMBASE`, `7` = scratch, `8` = `op`, `9` = `arg`.  Decode
`(op, arg)`, advance `pp += 2`, compute `MEMBASE + arg` into cell `7`, then dispatch: `op = 0` ↦ `sacc := arg`;
`op ≠ 0` ↦ `simMem[arg] := sacc`.  Both branches cost `19`. -/
def asmMem : List Instr :=
  [ .loadIndI 5, .storeI 8, .loadI 5, .addI 2, .storeI 7, .loadIndI 7, .storeI 9,
    .loadI 5, .addI 3, .storeI 5, .loadI 6, .addI 9, .storeI 7, .loadI 8, .jzI 18,
    .loadI 1, .storeIndI 7, .jmpI 21, .loadI 9, .storeI 1, .jmpI 21, .jmpI 0 ]

/-- Aligned state: not halted, real `pc` at the loop head, the two constants in place, and the program pointer and
memory base high enough (`8 ≤ pp`, `8 ≤ MEMBASE`) that program and image cells are disjoint from the control cells. -/
def AsmMemAligned (s : State) : Prop :=
  s.halted = false ∧ s.pc = 0 ∧ s.mem 2 = 1 ∧ s.mem 3 = 2 ∧ 8 ≤ s.mem 5 ∧ 8 ≤ s.mem 6

/-- The common prefix memory after the `(op, arg)` decode, pointer advance, and address computation. -/
def asmMemP (s : State) : Mem :=
  ((((s.mem.set 8 (s.mem (s.mem 5))).set 7 (s.mem 5 + 1)).set 9 (s.mem (s.mem 5 + 1))).set 5 (s.mem 5 + 2)).set 7
    (s.mem 6 + s.mem (s.mem 5 + 1))

/-- The macro-step `asmMem` realises: decode `(op, arg)` at `pp`, `pp += 2`, and — dispatching on `op` — either set
`sacc := arg` (`op = 0`) or write the simulated memory image `simMem[arg] := sacc` (`op ≠ 0`). -/
def asmMemMstep (s : State) : State :=
  { mem := if s.mem (s.mem 5) = 0 then (asmMemP s).set 1 (s.mem (s.mem 5 + 1))
           else (asmMemP s).set (s.mem 6 + s.mem (s.mem 5 + 1)) (s.mem 1),
    acc := if s.mem (s.mem 5) = 0 then s.mem (s.mem 5 + 1) else s.mem 1,
    pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost with a memory handler in the dispatch (proved)**: from an aligned state, one macro-step
runs in exactly `19` real steps — the immediate branch and the memory-writing branch cost the same. -/
theorem asmMem_step (s : State) (h : AsmMemAligned s) : run asmMem s 19 = asmMemMstep s := by
  obtain ⟨hh, hpc, hc, hc3, hb5, hb6⟩ := h
  by_cases hop : s.mem (s.mem 5) = 0
  · simp [run, step, asmMem, hh, hpc, hc, hc3, asmMemMstep, asmMemP, hop,
      show s.mem 5 + 1 ≠ 7 by omega, show s.mem 5 + 1 ≠ 8 by omega]
  · simp [run, step, asmMem, hh, hpc, hc, hc3, asmMemMstep, asmMemP, hop,
      show s.mem 5 + 1 ≠ 7 by omega, show s.mem 5 + 1 ≠ 8 by omega]

/-- The macro-step preserves the aligned invariant (the image write at `MEMBASE + arg ≥ 8` misses control cells `2`,
`3`, `5`, `6`, discharged by `omega`). -/
theorem asmMemMstep_pres (s : State) (h : AsmMemAligned s) : AsmMemAligned (asmMemMstep s) := by
  obtain ⟨hh, hpc, hc, hc3, hb5, hb6⟩ := h
  have h5 : (asmMemMstep s).mem 5 = s.mem 5 + 2 := by
    by_cases hop : s.mem (s.mem 5) = 0 <;>
      simp [asmMemMstep, asmMemP, hop, show (5 : ℕ) ≠ s.mem 6 + s.mem (s.mem 5 + 1) by omega]
  refine ⟨hh, rfl, ?_, ?_, ?_, ?_⟩
  · by_cases hop : s.mem (s.mem 5) = 0 <;>
      simp [asmMemMstep, asmMemP, hop, hc, show (2 : ℕ) ≠ s.mem 6 + s.mem (s.mem 5 + 1) by omega]
  · by_cases hop : s.mem (s.mem 5) = 0 <;>
      simp [asmMemMstep, asmMemP, hop, hc3, show (3 : ℕ) ≠ s.mem 6 + s.mem (s.mem 5 + 1) by omega]
  · rw [h5]; omega
  · by_cases hop : s.mem (s.mem 5) = 0 <;>
      simp [asmMemMstep, asmMemP, hop, hb6, show (6 : ℕ) ≠ s.mem 6 + s.mem (s.mem 5 + 1) by omega]

/-- **Linear clocking overhead with a memory handler in the dispatch (proved)**: `k` assembled macro-steps run in
exactly `19k` real steps. -/
theorem asmMem_iterate (k : ℕ) (s : State) (h : AsmMemAligned s) :
    run asmMem s (k * 19) = asmMemMstep^[k] s :=
  run_macro_iterate asmMem asmMemMstep 19 AsmMemAligned asmMemMstep_pres asmMem_step k s h

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.asmMem_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.asmMem_iterate
