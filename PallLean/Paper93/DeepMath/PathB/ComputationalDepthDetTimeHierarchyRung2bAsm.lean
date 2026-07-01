import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDetTimeHierarchyRung2b

/-!
# Time hierarchy, rung 2b (assembly): one interpreter decoding `(op, arg)` and dispatching, uniform cost

The scale-up's separate mechanisms are proved: single-opcode fetch and dispatch (`…Rung2bInterp`) and simulated-memory
read/write (`…Rung2bMem`).  This file **assembles** them into one interpreter that does what `uStepFn` (rung 2a) does at
its core — **decode a full `(op, arg)` instruction from the program and dispatch to distinct handlers** — all in a
single loop with **one uniform per-macro-step cost**, feeding the linear-overhead backbone.

  `asmInterp` — a real `List Instr` interpreter: fetch `op = mem[pp]` and `arg = mem[pp+1]` from the program image,
        advance the program pointer `pp += 2`, dispatch on `op` (a real `jzI` branch), run the matching handler
        (`op = 0`: `sacc := arg`; `op ≠ 0`: `sacc := sacc + arg`), both handlers **padded to the uniform cost 17**.
  `asmInterp_step` — **PROVED**: from an aligned state, one assembled macro-step (two-field decode + dispatch + handler
        + pointer advance) runs in exactly `17` real steps and yields `asmMstep s`, on *either* dispatch branch.
  `asmMstep_pres` / `asmInterp_iterate` — **PROVED**: the macro-step preserves the aligned invariant, and `k` assembled
        macro-steps run in exactly `17k` real steps.

This is the decode-and-dispatch backbone of `uStepFn` realised as one uniform-cost `List Instr` program: a genuine
two-field instruction decode, a real opcode branch to distinct handlers, and a proved exact per-step cost.

## Honest scope

`asmInterp` decodes `(op, arg)` and dispatches to two representative handlers (immediate-set and immediate-add) with a
uniform cost — the assembly backbone.  The **full** ten-opcode `uStepFn` is the remaining mechanical work: fold the
other handlers into the same dispatch — the memory-image `loadI`/`storeI` (proved in `…Rung2bMem`), the double-indirect
`loadIndI`/`storeIndI`, arithmetic `addI`/`subI` over the image, and control `jzI`/`jmpI`/`haltI` on the simulated
`pc` — each **padded to the one uniform cost**, and prove the assembled macro-step equals `uStepFn`.  Every ingredient
(two-field decode, dispatch, memory image, uniform-cost padding, linear overhead) is now a proved `List Instr`
mechanism; what remains is repeating this pattern across all ten opcodes.  Then `run_macro_iterate` gives
`run uProg s (k·17-ish) = k` faithful `uStepFn` steps, feeding rung 1's `UniversalRAMRealizesDiagonal` to close the
*deterministic* hierarchy; the *nondeterministic* lift (lazy diagonalisation) remains.  Nothing here is
`NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-- The **assembled** interpreter.  Cells: `1` = `sacc`, `2` = const `1`, `3` = const `2`, `5` = program pointer `pp`,
`7` = scratch, `8` = fetched `op`, `9` = fetched `arg`.  Each iteration decodes `op = mem[pp]` and `arg = mem[pp+1]`,
advances `pp += 2`, then dispatches on `op`: `0` ↦ `sacc := arg`, else ↦ `sacc := sacc + arg`.  Both handlers are padded
to the same length so every macro-step costs exactly `17`. -/
def asmInterp : List Instr :=
  [ .loadIndI 5, .storeI 8, .loadI 5, .addI 2, .storeI 7, .loadIndI 7, .storeI 9,
    .loadI 5, .addI 3, .storeI 5, .loadI 8, .jzI 16,
    .loadI 1, .addI 9, .storeI 1, .jmpI 20,
    .loadI 9, .storeI 1, .loadI 2, .jmpI 20, .jmpI 0 ]

/-- Aligned state for the assembled interpreter: not halted, real `pc` at the loop head, the two constants in place, and
the program pointer high enough (`8 ≤ pp`) that program cells are disjoint from control cells. -/
def AsmAligned (s : State) : Prop :=
  s.halted = false ∧ s.pc = 0 ∧ s.mem 2 = 1 ∧ s.mem 3 = 2 ∧ 8 ≤ s.mem 5

/-- The macro-step `asmInterp` realises: decode `(op, arg)` at `pp`, `pp += 2`, and set `sacc` to `arg` if `op = 0` else
`sacc + arg`. -/
def asmMstep (s : State) : State :=
  { mem := (((s.mem.set 8 (s.mem (s.mem 5))).set 7 (s.mem 5 + 1)).set 9 (s.mem (s.mem 5 + 1))).set 5 (s.mem 5 + 2)
             |>.set 1 (if s.mem (s.mem 5) = 0 then s.mem (s.mem 5 + 1) else s.mem 1 + s.mem (s.mem 5 + 1)),
    acc := if s.mem (s.mem 5) = 0 then s.mem 2 else s.mem 1 + s.mem (s.mem 5 + 1),
    pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost of the assembled decode+dispatch (proved)**: from an aligned state, one full macro-step
— two-field `(op, arg)` decode, program-pointer advance, opcode dispatch, and the matching handler — runs in exactly
`17` real steps, on *either* branch of the dispatch. -/
theorem asmInterp_step (s : State) (h : AsmAligned s) : run asmInterp s 17 = asmMstep s := by
  obtain ⟨hh, hpc, hc2, hc3, hb⟩ := h
  by_cases hop : s.mem (s.mem 5) = 0
  · simp [run, step, asmInterp, hh, hpc, hc2, hc3, asmMstep, hop,
      show s.mem 5 + 1 ≠ 7 by omega, show s.mem 5 + 1 ≠ 8 by omega]
  · simp [run, step, asmInterp, hh, hpc, hc2, hc3, asmMstep, hop,
      show s.mem 5 + 1 ≠ 7 by omega, show s.mem 5 + 1 ≠ 8 by omega]

/-- The assembled macro-step preserves the aligned invariant. -/
theorem asmMstep_pres (s : State) (h : AsmAligned s) : AsmAligned (asmMstep s) := by
  obtain ⟨hh, hpc, hc2, hc3, hb⟩ := h
  refine ⟨hh, rfl, by simp [asmMstep, hc2], by simp [asmMstep, hc3], ?_⟩
  have h5 : (asmMstep s).mem 5 = s.mem 5 + 2 := by simp [asmMstep]
  rw [h5]; omega

/-- **Linear clocking overhead of the assembled interpreter (proved)**: `k` decode+dispatch macro-steps run in exactly
`17k` real steps. -/
theorem asmInterp_iterate (k : ℕ) (s : State) (h : AsmAligned s) :
    run asmInterp s (k * 17) = asmMstep^[k] s :=
  run_macro_iterate asmInterp asmMstep 17 AsmAligned asmMstep_pres asmInterp_step k s h

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.asmInterp_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.asmInterp_iterate
