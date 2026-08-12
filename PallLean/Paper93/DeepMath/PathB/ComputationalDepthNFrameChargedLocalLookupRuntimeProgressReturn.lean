import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeMarkerDrivenClear

/-!
# Fixed reverse return to an on-tape progress mark

The outer universal shift loop cannot use an all-zero record: zero is also
the tape blank and supplies no physical exhaustion signal.  The sound record
uses `10` for an ordinary remaining pass and `01` for the final pass.  Neither
word occurs inside a passed block except its terminal `01`, and reverse scan
starts to the left of the trailing hole after crossing that terminal.

This file supplies the fixed reverse controller.  It scans pairwise to the
left, recognizes `10`, clears it to `00`, and halts at the consumed mark.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn

set_option maxHeartbeats 4000000

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeProgressReturnState
  | enter
  | hi
  | lo (hiBit : Bool)
  | clearHi
  | done
  deriving DecidableEq, Fintype

/-- Fixed reverse pair scanner for the ordinary `10` progress word. -/
def runtimeProgressReturnMachine : Machine where
  State := RuntimeProgressReturnState
  fin := inferInstance
  dec := inferInstance
  start := .enter
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .enter => (.hi, none, 0)
    | .hi => (.lo b, none, 0)
    | .lo hiBit =>
        if b && !hiBit then (.clearHi, some false, 1)
        else (.hi, none, 0)
    | .clearHi => (.done, some false, 0)
    | .done => (.done, none, 2)
  accept := fun _ => false

private theorem progress_write_lo (pre tail : List Bool) :
    writeAt (pre ++ [true, false] ++ tail) pre.length false =
      pre ++ [false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem progress_write_hi (pre tail : List Bool) :
    writeAt (pre ++ [false, false] ++ tail) (pre.length + 1) false =
      pre ++ [false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem progress_hi_step (T : List Bool) (p : Nat) (b : Bool)
    (hread : T[p + 1]?.getD false = b) :
    step runtimeProgressReturnMachine
        ⟨RuntimeProgressReturnState.hi, p + 1, T⟩ =
      ⟨RuntimeProgressReturnState.lo b, p, T⟩ := by
  simp [step, runtimeProgressReturnMachine, moveHead, hread]

private theorem progress_lo_marker_step (T T' : List Bool) (p : Nat)
    (hread : T[p]?.getD false = true)
    (hwrite : writeAt T p false = T') :
    step runtimeProgressReturnMachine
        ⟨RuntimeProgressReturnState.lo false, p, T⟩ =
      ⟨RuntimeProgressReturnState.clearHi, p + 1, T'⟩ := by
  simp [step, runtimeProgressReturnMachine, moveHead, hread, hwrite]

private theorem progress_clear_step (T T' : List Bool) (p : Nat)
    (hwrite : writeAt T (p + 1) false = T') :
    step runtimeProgressReturnMachine
        ⟨RuntimeProgressReturnState.clearHi, p + 1, T⟩ =
      ⟨RuntimeProgressReturnState.done, p, T'⟩ := by
  simp [step, runtimeProgressReturnMachine, moveHead, hwrite]

/-- Enter reverse scanning from the low cell of the trailing hole. -/
theorem runtimeProgressReturn_enter (T : List Bool) (p : Nat) :
    run runtimeProgressReturnMachine 1
        ⟨runtimeProgressReturnMachine.start, p, T⟩ =
      ⟨RuntimeProgressReturnState.hi, p - 1, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, runtimeProgressReturnMachine, moveHead]

/-- One non-marker pair is crossed right-to-left in two transitions. -/
theorem runtimeProgressReturn_nonmarker
    (pre tail : List Bool) (lo hi : Bool)
    (hnm : ¬ (lo = true ∧ hi = false)) :
    run runtimeProgressReturnMachine 2
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨RuntimeProgressReturnState.hi, pre.length - 1,
        pre ++ [lo, hi] ++ tail⟩ := by
  rw [run_succ, run_succ, run_zero]
  cases lo <;> cases hi <;>
    simp_all [step, runtimeProgressReturnMachine, moveHead,
      List.getD_eq_getElem?_getD]

/-- The ordinary `10` progress word is consumed to `00`; the controller
returns to its low cell and genuinely halts. -/
theorem runtimeProgressReturn_marker (pre tail : List Bool) :
    run runtimeProgressReturnMachine 3
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [true, false] ++ tail⟩ =
      ⟨RuntimeProgressReturnState.done, pre.length,
        pre ++ [false, false] ++ tail⟩ := by
  let T0 := pre ++ [true, false] ++ tail
  let T1 := pre ++ [false, false] ++ tail
  have hhi : T0[pre.length + 1]?.getD false = false := by simp [T0]
  have hlo : T0[pre.length]?.getD false = true := by simp [T0]
  have hw0 : writeAt T0 pre.length false = T1 := by
    simpa [T0, T1] using progress_write_lo pre tail
  have hw1 : writeAt T1 (pre.length + 1) false = T1 := by
    simpa [T1] using progress_write_hi pre tail
  change run runtimeProgressReturnMachine 3
      ⟨RuntimeProgressReturnState.hi, pre.length + 1, T0⟩ =
    ⟨RuntimeProgressReturnState.done, pre.length, T1⟩
  rw [show run runtimeProgressReturnMachine 3
      ⟨RuntimeProgressReturnState.hi, pre.length + 1, T0⟩ =
      step runtimeProgressReturnMachine
        (step runtimeProgressReturnMachine
          (step runtimeProgressReturnMachine
            ⟨RuntimeProgressReturnState.hi, pre.length + 1, T0⟩)) by rfl]
  rw [progress_hi_step T0 pre.length false hhi,
    progress_lo_marker_step T0 T1 pre.length hlo hw0,
    progress_clear_step T1 T1 pre.length hw1]

/-- Consuming a progress word is left-safe even when the word begins at the
physical origin: the only left moves start from its high cell. -/
theorem runtimeProgressReturn_marker_leftSafe (pre tail : List Bool) :
    LeftSafeRun runtimeProgressReturnMachine
      ⟨RuntimeProgressReturnState.hi, pre.length + 1,
        pre ++ [true, false] ++ tail⟩ 3 := by
  intro i hi _ hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressReturnMachine, moveHead,
      List.getD_eq_getElem?_getD, writeAt] at hmove ⊢

@[simp] theorem runtimeProgressReturn_done_halts :
    runtimeProgressReturnMachine.halt RuntimeProgressReturnState.done = true := by
  simp [runtimeProgressReturnMachine]

#print axioms runtimeProgressReturn_enter
#print axioms runtimeProgressReturn_nonmarker
#print axioms runtimeProgressReturn_marker
#print axioms runtimeProgressReturn_marker_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn
