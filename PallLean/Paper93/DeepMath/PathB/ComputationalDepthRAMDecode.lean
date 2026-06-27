import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDP
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — decode & dispatch, verified (PROVED) — step 2, brick 1

Step 1 built the memo DP as a real RAM program.  Step 2 builds the **lazy diagonal decider**: the machine that,
on an input encoding a machine index, decodes the fields, then **dispatches** to either a *copy* branch
(behave like the simulated machine) or a *boundary/complement* branch (flip the bit, to diagonalise).  This
brick is the front end — **decode the packed input and dispatch on the mode flag** — and proves that the
fields are decoded correctly, the branch is routed correctly, and the complement branch genuinely flips the
input bit (the diagonal seed).

Input region / registers (concrete addresses, so disjointness is automatic):

  `mem[10]=idx  mem[11]=code  mem[12]=inp  mem[13]=mode`   (packed input)
  `mem[0]=idx' mem[1]=code'  mem[2]=inp'  mem[3]=mode'  mem[4]=result`   (decoded registers + result)

```
  0..7:  decode — copy mem[10..13] into mem[0..3]
  8: loadI 3   9: jzI 13                  -- dispatch on mode'
  10: constI 1 11: subI 2  12: jmpI 14    -- complement branch: result := 1 - inp'
  13: loadI 2                             -- copy branch:       result := inp'
  14: storeI 4 15: haltI                  -- converge: store result, halt
```

  `decode_state` — the exact machine state after the `8`-step decode phase.
  `decodeDispatch_decode` — after decode, `mem[0..3]` hold `mem[10..13]`.
  `decodeDispatch_copy` — `mode = 0`: halts after exactly `13` steps with `result = inp` (copy/echo branch).
  `decodeDispatch_complement` — `mode ≠ 0`: halts after exactly `15` steps with `result = 1 - inp` (flip).
  `decodeDispatch_diagonal` — on a complement input with `inp ∈ {0,1}`, the result **differs** from `inp`: the
        decider disagrees with the echoed value — the essence of the diagonal flip.

The runs are split with `run_add` (decode phase + dispatch phase) so each evaluation stays small.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This is the decode/dispatch front end of the diagonal decider; the copy branch
will later invoke the simulator/clock and the complement branch the boundary action.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The decode-and-dispatch front end of the lazy diagonal decider. -/
def decodeDispatch : List Instr :=
  [ Instr.loadI 10, Instr.storeI 0       -- 0,1:  idx'  := idx
  , Instr.loadI 11, Instr.storeI 1       -- 2,3:  code' := code
  , Instr.loadI 12, Instr.storeI 2       -- 4,5:  inp'  := inp
  , Instr.loadI 13, Instr.storeI 3       -- 6,7:  mode' := mode
  , Instr.loadI 3, Instr.jzI 13          -- 8,9:  dispatch on mode'
  , Instr.constI 1, Instr.subI 2, Instr.jmpI 14  -- 10,11,12: complement → result := 1 - inp'
  , Instr.loadI 2                         -- 13:   copy → result := inp'
  , Instr.storeI 4, Instr.haltI ]         -- 14,15: store result, halt

/-- **The exact state after the `8`-step decode phase**: registers `mem[0..3]` loaded from `mem[10..13]`,
`pc = 8`, not halted. -/
theorem decode_state (m : Mem) (acc : ℕ) :
    run decodeDispatch ⟨m, acc, 0, false⟩ 8 = ⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩ := by
  show step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (⟨m, acc, 0, false⟩)))))))) = _
  simp [step, decodeDispatch, List.getD]

/-- **Decode is correct**: after the decode phase the registers `mem[0..3]` hold the input fields
`mem[10..13]`. -/
theorem decodeDispatch_decode (m : Mem) (acc : ℕ) :
    (run decodeDispatch ⟨m, acc, 0, false⟩ 8).mem 0 = m 10
      ∧ (run decodeDispatch ⟨m, acc, 0, false⟩ 8).mem 1 = m 11
      ∧ (run decodeDispatch ⟨m, acc, 0, false⟩ 8).mem 2 = m 12
      ∧ (run decodeDispatch ⟨m, acc, 0, false⟩ 8).mem 3 = m 13 := by
  rw [decode_state]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- **Copy branch**: when `mode = 0`, the decider halts after exactly `13` steps with `result = inp` — it echoes
the input (the "simulate" branch placeholder). -/
theorem decodeDispatch_copy (m : Mem) (acc : ℕ) (hmode : m 13 = 0) :
    (run decodeDispatch ⟨m, acc, 0, false⟩ 13).halted = true
      ∧ (run decodeDispatch ⟨m, acc, 0, false⟩ 13).mem 4 = m 12 := by
  have hrw : run decodeDispatch ⟨m, acc, 0, false⟩ 13
      = run decodeDispatch ⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩ 5 := by
    rw [show (13 : ℕ) = 8 + 5 from rfl, run_add, decode_state]
  rw [hrw]
  refine ⟨?_, ?_⟩
  · show (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩)))))).halted = true
    simp [step, decodeDispatch, List.getD, hmode]
  · show (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩)))))).mem 4 = m 12
    simp [step, decodeDispatch, List.getD, hmode]

/-- **Complement branch**: when `mode ≠ 0`, the decider halts after exactly `15` steps with `result = 1 - inp`
— it flips the input bit (the boundary/diagonal branch). -/
theorem decodeDispatch_complement (m : Mem) (acc : ℕ) (hmode : m 13 ≠ 0) :
    (run decodeDispatch ⟨m, acc, 0, false⟩ 15).halted = true
      ∧ (run decodeDispatch ⟨m, acc, 0, false⟩ 15).mem 4 = 1 - m 12 := by
  have hrw : run decodeDispatch ⟨m, acc, 0, false⟩ 15
      = run decodeDispatch ⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩ 7 := by
    rw [show (15 : ℕ) = 8 + 7 from rfl, run_add, decode_state]
  rw [hrw]
  refine ⟨?_, ?_⟩
  · show (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩)))))))).halted = true
    simp [step, decodeDispatch, List.getD, hmode]
  · show (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (step decodeDispatch (⟨(((m.set 0 (m 10)).set 1 (m 11)).set 2 (m 12)).set 3 (m 13), m 13, 8, false⟩)))))))).mem 4 = 1 - m 12
    simp [step, decodeDispatch, List.getD, hmode]

/-- **The diagonal flip**: on a complement input with a boolean `inp ∈ {0,1}`, the decider's result *differs*
from `inp`.  This is the essence of diagonalisation — the output disagrees with the echoed value. -/
theorem decodeDispatch_diagonal (m : Mem) (acc : ℕ) (hmode : m 13 ≠ 0) (hbit : m 12 ≤ 1) :
    (run decodeDispatch ⟨m, acc, 0, false⟩ 15).mem 4 ≠ m 12 := by
  have h := (decodeDispatch_complement m acc hmode).2
  rw [h]; omega

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.decode_state
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.decodeDispatch_copy
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.decodeDispatch_complement
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.decodeDispatch_diagonal
