import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDetTimeHierarchyRung2b

/-!
# Time hierarchy, rung 2b (interpreter half): a real `List Instr` interpreter with fetch, dispatch, and cost

Rung 2b's cost half (`…Rung2b`) proved the clocking-overhead backbone (`run_macro_iterate`: a uniform-cost clocked
interpreter runs `k` macro-steps in exactly `k · cost` real steps).  This file supplies the **interpreter half** on the
real RAM machine: genuine `List Instr` programs that

  * **fetch** a simulated instruction from a *program image* in memory at a moving program pointer (via the RAM's
    indirect addressing `loadIndI`), and
  * **dispatch** on the fetched opcode to distinct handlers (a real `jzI` branch, handlers **padded to a uniform step
    count**),

each with its **exact per-macro-step cost proved**, then composed through `run_macro_iterate` to a linear clocking
overhead.

  `fetchInterp` / `fetchInterp_step` / `fetchInterp_iterate` — a fetch-execute interpreter (`sacc += mem[progptr]`,
        `progptr += 1`, loop): reads a *different* program cell each step via indirect addressing, exact cost `7`,
        `k` steps in exactly `7k`.
  `dispInterp` / `dispInterp_step` / `dispInterp_iterate` — a **dispatch** interpreter (`if opcode = 0 then sacc += 1
        else sacc -= 1`, `progptr += 1`, loop): a real two-way `jzI` branch with both handlers padded to the uniform
        cost `10`, `k` steps in exactly `10k`.

This is the ISA-level realisation of the fetch–decode–execute cycle: instructions read from a memory image, a real
opcode dispatch, and a proved exact per-step cost feeding the linear-overhead backbone.

## Honest scope

These are genuine `List Instr` interpreters with indirect-addressed fetch, real opcode dispatch, uniform-cost padding,
and proved linear clocking overhead — the mechanisms rung 2b's interpreter half needs, demonstrated end-to-end on the
real RAM `run`.  They simulate a small accumulator ISA, **not** yet the full ten-opcode RAM `uStepFn` of rung 2a: the
remaining work is the mechanical extension to all ten handlers over a full memory image (decoding `(op,arg)`, indirect
loads/stores for simulated memory, every handler padded to one uniform cost) — the same three mechanisms shown here,
scaled up.  Once that per-macro-step matches `uStepFn`, `run_macro_iterate` gives `run uProg s (k·cost) = k` faithful
`uStepFn` steps, feeding rung 1's `UniversalRAMRealizesDiagonal` to close the *deterministic* hierarchy; the
*nondeterministic* lift (lazy diagonalisation) remains.  Nothing here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-! ### A fetch-execute interpreter: indirect fetch from a program image -/

/-- A fetch-execute interpreter.  Memory layout: cell `1` = simulated accumulator, cell `2` = constant `1`,
cell `5` = program pointer (a real address into the program image).  Each loop iteration fetches the opcode at the
program pointer (`loadIndI 5` reads `mem[mem[5]]`), adds it to the accumulator, advances the pointer, and loops. -/
def fetchInterp : List Instr :=
  [ .loadIndI 5, .addI 1, .storeI 1, .loadI 5, .addI 2, .storeI 5, .jmpI 0 ]

/-- Aligned interpreter state: not halted, real `pc` at the loop head, constant cell holds `1`. -/
def FetchAligned (s : State) : Prop := s.halted = false ∧ s.pc = 0 ∧ s.mem 2 = 1

/-- The macro-step `fetchInterp` realises: `sacc += mem[progptr]`, `progptr += 1`. -/
def fetchMstep (s : State) : State :=
  { mem := (s.mem.set 1 (s.mem (s.mem 5) + s.mem 1)).set 5 (s.mem 5 + 1),
    acc := s.mem 5 + 1, pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost (proved)**: from an aligned state, `fetchInterp` runs one fetch-execute macro-step in
exactly `7` real steps — including the indirect fetch from the program image. -/
theorem fetchInterp_step (s : State) (h : FetchAligned s) : run fetchInterp s 7 = fetchMstep s := by
  obtain ⟨hh, hpc, hc⟩ := h
  simp [run, step, fetchInterp, hh, hpc, hc, fetchMstep]

/-- The fetch-execute macro-step preserves the aligned invariant. -/
theorem fetchMstep_pres (s : State) (h : FetchAligned s) : FetchAligned (fetchMstep s) := by
  refine ⟨h.1, rfl, ?_⟩
  simp [fetchMstep, h.2.2]

/-- **Linear clocking overhead (proved)**: `k` fetch-execute macro-steps run in *exactly* `7k` real steps. -/
theorem fetchInterp_iterate (k : ℕ) (s : State) (h : FetchAligned s) :
    run fetchInterp s (k * 7) = fetchMstep^[k] s :=
  run_macro_iterate fetchInterp fetchMstep 7 FetchAligned fetchMstep_pres fetchInterp_step k s h

/-! ### A dispatch interpreter: a real opcode branch with uniform-cost handlers -/

/-- A dispatch interpreter.  Fetches the opcode at the program pointer and **branches** (`jzI`): opcode `0` ↦ `sacc += 1`
(handler at pc `6`), else ↦ `sacc -= 1` (handler at pc `2`); both handlers are **padded to the same length**, then a
common tail advances the program pointer and loops.  Every path runs in exactly `10` real steps. -/
def dispInterp : List Instr :=
  [ .loadIndI 5, .jzI 6, .loadI 1, .subI 2, .storeI 1, .jmpI 10,
    .loadI 1, .addI 2, .storeI 1, .jmpI 10, .loadI 5, .addI 2, .storeI 5, .jmpI 0 ]

/-- The macro-step `dispInterp` realises: `sacc += 1` if `opcode = 0` else `sacc -= 1`, then `progptr += 1`. -/
def dispMstep (s : State) : State :=
  { mem := (s.mem.set 1 (if s.mem (s.mem 5) = 0 then s.mem 1 + 1 else s.mem 1 - 1)).set 5 (s.mem 5 + 1),
    acc := s.mem 5 + 1, pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost with dispatch (proved)**: from an aligned state, `dispInterp` runs one macro-step in
exactly `10` real steps on *either* branch of the opcode dispatch (handlers padded to a uniform cost). -/
theorem dispInterp_step (s : State) (h : FetchAligned s) : run dispInterp s 10 = dispMstep s := by
  obtain ⟨hh, hpc, hc⟩ := h
  by_cases hop : s.mem (s.mem 5) = 0
  · simp [run, step, dispInterp, hh, hpc, hc, dispMstep, hop]
  · simp [run, step, dispInterp, hh, hpc, hc, dispMstep, hop]

/-- The dispatch macro-step preserves the aligned invariant. -/
theorem dispMstep_pres (s : State) (h : FetchAligned s) : FetchAligned (dispMstep s) := by
  refine ⟨h.1, rfl, ?_⟩
  simp [dispMstep, h.2.2]

/-- **Linear clocking overhead with dispatch (proved)**: `k` dispatch macro-steps run in *exactly* `10k` real steps. -/
theorem dispInterp_iterate (k : ℕ) (s : State) (h : FetchAligned s) :
    run dispInterp s (k * 10) = dispMstep^[k] s :=
  run_macro_iterate dispInterp dispMstep 10 FetchAligned dispMstep_pres dispInterp_step k s h

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.fetchInterp_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.fetchInterp_iterate
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.dispInterp_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.dispInterp_iterate
