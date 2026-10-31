import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMModel

/-!
# Time hierarchy, rung 2a: the universal interpreter's transition, faithful for *all* opcodes

Rung 1 (`…DetTimeHierarchyRung1`) grounded the deterministic hierarchy on the real RAM `run` and isolated the single
remaining computational lemma: a **universal RAM interpreter** that simulates any program within a bounded budget (the
repo's `uSim` only simulates a *counting* machine).  Building that interpreter is rung 2; this file is **sub-rung 2a** —
the interpreter's fetch–decode–execute *transition*, proved faithful for **every** opcode (including indirect
addressing), for **any** program and **any** number of steps.

  `encodeInstr` / `decodeInstr` / `decode_encode` — a codec putting each `Instr` as an `(opcode, arg)` pair, with the
        round-trip `decodeInstr (encodeInstr i) = i` (proved).  This is how the interpreter reads a program from memory.
  `uStepFn` — one **universal step**: fetch `(op, arg)` at the simulated `pc` from an encoded program table, decode, and
        dispatch — the interpreter's transition, mirroring `step` across all ten instructions.
  `uStepFn_correct` — **PROVED**: over a program stored via `encodeInstr`, one `uStepFn` reproduces one real `step`
        (all opcodes, indirect addressing included).
  `uRunFn` / `uRunFn_correct` — **PROVED**: iterating the universal step for `k` rounds reproduces `run progL s k` for
        every program `progL`, state `s`, and step count `k`.  The interpreter's transition is faithful over full runs.

## Honest scope

This proves the universal interpreter's **transition is correct for all opcodes and all runs** — the specification any
ISA-level interpreter must meet.  `uStepFn`/`uRunFn` are still Lean *functions*, not a `List Instr` RAM program: the
remaining sub-rungs are (2b) realising `uStepFn` as actual `Instr` operating on encoded memory with a **bounded
per-step cost** (the clocking overhead), and (2c) feeding that back into rung 1's `UniversalRAMRealizesDiagonal` to
close the deterministic hierarchy.  Then the *nondeterministic* lift (lazy diagonalisation) remains.  This is sub-rung
2a, not the interpreter and not the hierarchy.  Nothing here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-! ### Instruction codec: an `(opcode, arg)` encoding the interpreter reads from memory -/

/-- Encode an instruction as an `(opcode, argument)` pair. -/
def encodeInstr : Instr → ℕ × ℕ
  | .constI v => (0, v) | .loadI a => (1, a) | .storeI a => (2, a)
  | .loadIndI a => (3, a) | .storeIndI a => (4, a) | .addI a => (5, a)
  | .subI a => (6, a) | .jzI t => (7, t) | .jmpI t => (8, t) | .haltI => (9, 0)

/-- Decode an `(opcode, argument)` pair back to an instruction (out-of-range opcode ↦ `halt`). -/
def decodeInstr (op arg : ℕ) : Instr :=
  match op with
  | 0 => .constI arg | 1 => .loadI arg | 2 => .storeI arg | 3 => .loadIndI arg
  | 4 => .storeIndI arg | 5 => .addI arg | 6 => .subI arg | 7 => .jzI arg
  | 8 => .jmpI arg | _ => .haltI

/-- **Codec round-trip (proved)**: decoding an encoded instruction recovers it. -/
theorem decode_encode (i : Instr) : decodeInstr (encodeInstr i).1 (encodeInstr i).2 = i := by
  cases i <;> rfl

/-! ### The universal step: fetch–decode–execute over an encoded program table -/

/-- One **universal step**: at the simulated `pc`, fetch `(op, arg)` from the encoded program table `prog`, decode, and
apply the instruction — the interpreter's transition, dispatching over all ten opcodes (with indirect addressing). -/
def uStepFn (prog : ℕ → ℕ × ℕ) (s : State) : State :=
  if s.halted then s else
  match decodeInstr (prog s.pc).1 (prog s.pc).2 with
  | .constI v    => { s with acc := v, pc := s.pc + 1 }
  | .loadI a     => { s with acc := s.mem a, pc := s.pc + 1 }
  | .storeI a    => { s with mem := s.mem.set a s.acc, pc := s.pc + 1 }
  | .loadIndI a  => { s with acc := s.mem (s.mem a), pc := s.pc + 1 }
  | .storeIndI a => { s with mem := s.mem.set (s.mem a) s.acc, pc := s.pc + 1 }
  | .addI a      => { s with acc := s.acc + s.mem a, pc := s.pc + 1 }
  | .subI a      => { s with acc := s.acc - s.mem a, pc := s.pc + 1 }
  | .jzI t       => { s with pc := if s.acc = 0 then t else s.pc + 1 }
  | .jmpI t      => { s with pc := t }
  | .haltI       => { s with halted := true }

/-- **The universal step is faithful (proved)**: over a program stored via `encodeInstr`, one `uStepFn` reproduces one
real `step` — for every opcode, indirect addressing included. -/
theorem uStepFn_correct (progL : List Instr) (s : State) :
    uStepFn (fun i => encodeInstr (progL.getD i .haltI)) s = step progL s := by
  simp only [uStepFn, step]
  by_cases h : s.halted = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, decode_encode]
    cases progL.getD s.pc Instr.haltI <;> rfl

/-- Iterate the universal step for `k` rounds. -/
def uRunFn (prog : ℕ → ℕ × ℕ) (s : State) : ℕ → State
  | 0 => s
  | k + 1 => uRunFn prog (uStepFn prog s) k

/-- **The universal interpreter's transition is faithful over full runs (proved)**: iterating `uStepFn` for `k` rounds
reproduces `run progL s k`, for every program, state, and step count. -/
theorem uRunFn_correct (progL : List Instr) (s : State) (k : ℕ) :
    uRunFn (fun i => encodeInstr (progL.getD i .haltI)) s k = run progL s k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show uRunFn (fun i => encodeInstr (progL.getD i .haltI)) (uStepFn _ s) k = run progL (step progL s) k
    rw [uStepFn_correct]
    exact ih (step progL s)

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.decode_encode
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.uStepFn_correct
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.uRunFn_correct
