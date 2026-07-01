import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMModel

/-!
# Time hierarchy, rung 2b: the clocking-overhead backbone (linear cost) on the real RAM

Rung 2a proved the universal interpreter's *transition* is faithful for all opcodes (as a Lean function `uStepFn`).
Rung 2b is the ISA-level realisation **with cost**: a fixed `List Instr` interpreter whose each macro-step runs in a
bounded number of real steps, so `k` simulated steps cost `O(k)` real steps (the clocking overhead).  This file builds
the **cost backbone** of that — proved on the real RAM `run` — and instantiates it on a genuine `List Instr` program
with an exact per-macro-step cost.

  `run_add` — **PROVED**: `run` composes, `run prog s (a+b) = run prog (run prog s a) b`.
  `run_macro_iterate` — **PROVED, the clocking-overhead argument**: for a fixed interpreter `prog` with an *aligned
        invariant* `P` (preserved by the macro-step `mstep`) and a **uniform per-macro-step cost** `cost`
        (`run prog s cost = mstep s`), running `k` macro-steps costs *exactly* `k * cost` real steps and yields
        `mstep^[k] s`.  This is the linear overhead: `k` simulated steps ⇒ `k · cost` real steps.
  `incProg` / `incProg_step` / `incProg_iterate` — a concrete `List Instr` clocked program with an **exact** macro-step
        cost of `4` real steps, instantiating the backbone: `k` iterations run in exactly `4k` steps.

## Honest scope

This proves the **cost half of 2b** on the real machine — the linear clocking overhead for any uniform-cost clocked
interpreter — and demonstrates it on genuine `List Instr` code with an exact per-step count.  It does **not** yet
realise the full `uStepFn` dispatch (rung 2a) as `List Instr`: that requires laying the simulated program/memory in a
memory image, coding the ten-way opcode dispatch as `Instr`, and **padding each handler to a uniform step count** so
`run_macro_iterate` applies.  That interpreter-realisation is the remaining half of 2b; combined with this backbone it
gives `run uProg s (k·cost) = <k faithful `uStepFn` steps>`, which feeds rung 1's `UniversalRAMRealizesDiagonal` to
close the *deterministic* hierarchy.  The *nondeterministic* lift (lazy diagonalisation) remains after that.  Nothing
here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-! ### `run` composition and the clocking-overhead argument -/

/-- **`run` composes (proved)**: running `a + b` steps is running `a` then `b`. -/
theorem run_add (prog : List Instr) (s : State) (a b : ℕ) :
    run prog s (a + b) = run prog (run prog s a) b := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih => rw [Nat.succ_add, run_succ, run_succ, ih]

/-- An invariant preserved by the macro-step is preserved by any number of macro-steps. -/
theorem iterate_pres {mstep : State → State} {P : State → Prop}
    (hpres : ∀ s, P s → P (mstep s)) : ∀ k s, P s → P (mstep^[k] s) := by
  intro k
  induction k with
  | zero => intro s hs; simpa using hs
  | succ k ih => intro s hs; rw [Function.iterate_succ_apply]; exact ih _ (hpres s hs)

/-- **The clocking-overhead argument (proved)**: for a fixed interpreter `prog` with an aligned invariant `P` preserved
by the macro-step `mstep`, and a *uniform* per-macro-step cost `cost` (each aligned macro-step runs in exactly `cost`
real steps), running `k` macro-steps costs *exactly* `k * cost` real steps and computes `mstep^[k]`.  This is the linear
clocking overhead: `k` simulated steps take `k · cost` real steps. -/
theorem run_macro_iterate (prog : List Instr) (mstep : State → State) (cost : ℕ) (P : State → Prop)
    (hpres : ∀ s, P s → P (mstep s)) (hstep : ∀ s, P s → run prog s cost = mstep s) :
    ∀ k s, P s → run prog s (k * cost) = mstep^[k] s := by
  intro k
  induction k with
  | zero => intro s _; simp [run]
  | succ k ih =>
      intro s hs
      rw [Nat.succ_mul, run_add, ih s hs, hstep (mstep^[k] s) (iterate_pres hpres k s hs),
        Function.iterate_succ_apply']

/-! ### A concrete clocked `List Instr` program with an exact per-macro-step cost -/

/-- The aligned invariant: not halted, and the simulated `pc` is at the loop head. -/
def Aligned (s : State) : Prop := s.halted = false ∧ s.pc = 0

/-- A concrete clocked `List Instr` program: load `mem[0]`, add `mem[1]`, store to `mem[0]`, jump back — one loop
iteration performs `mem[0] += mem[1]` and returns to the loop head. -/
def incProg : List Instr := [.loadI 0, .addI 1, .storeI 0, .jmpI 0]

/-- The macro-step `incProg` realises on aligned states. -/
def incMstep (s : State) : State :=
  { mem := s.mem.set 0 (s.mem 0 + s.mem 1), acc := s.mem 0 + s.mem 1, pc := 0, halted := s.halted }

/-- **Exact per-macro-step cost (proved)**: from an aligned state, `incProg` runs one macro-step in *exactly* `4` real
steps. -/
theorem incProg_step (s : State) (h : Aligned s) : run incProg s 4 = incMstep s := by
  obtain ⟨hh, hpc⟩ := h
  simp [run, step, incProg, hh, hpc, incMstep]

/-- The macro-step preserves the aligned invariant. -/
theorem incMstep_pres (s : State) (h : Aligned s) : Aligned (incMstep s) := ⟨h.1, rfl⟩

/-- **The backbone instantiated (proved)**: `k` iterations of the concrete clocked program run in *exactly* `4k` real
steps, computing `k` applications of the macro-step. -/
theorem incProg_iterate (k : ℕ) (s : State) (h : Aligned s) :
    run incProg s (k * 4) = incMstep^[k] s :=
  run_macro_iterate incProg incMstep 4 Aligned incMstep_pres incProg_step k s h

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.run_macro_iterate
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.incProg_step
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.incProg_iterate
