import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedOuterRound

/-!
# One fixed controller for the repeated outer shift

This controller internalizes the three certified phase machines.  Handoffs
preserve head and tape.  Exhaustion state `more` loops to the universal
forward pass; `final` enters the sole genuine halt state.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUniversalPassedShift
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn

inductive RuntimeFixedOuterControllerState
  | shift (s : RuntimeUniversalPassedShiftState)
  | ret (s : RuntimeProgressReturnState)
  | exhaust (s : RuntimeProgressExhaustState)
  | final
  deriving DecidableEq, Fintype

/-- The complete outer loop has one constant finite state type.  No payload,
record length, offset, schedule, or round number occurs in control. -/
def runtimeFixedOuterControllerMachine : Machine where
  State := RuntimeFixedOuterControllerState
  fin := inferInstance
  dec := inferInstance
  start := .shift runtimeUniversalPassedShiftMachine.start
  halt := fun s => decide (s = .final)
  δ := fun s b =>
    match s with
    | .shift ss =>
        if runtimeUniversalPassedShiftMachine.halt ss then
          (.ret runtimeProgressReturnMachine.start, none, 2)
        else
          let tr := runtimeUniversalPassedShiftMachine.δ ss b
          (.shift tr.1, tr.2.1, tr.2.2)
    | .ret sr =>
        if runtimeProgressReturnMachine.halt sr then
          (.exhaust runtimeProgressExhaustMachine.start, none, 2)
        else
          let tr := runtimeProgressReturnMachine.δ sr b
          (.ret tr.1, tr.2.1, tr.2.2)
    | .exhaust se =>
        if se = .more then
          (.shift runtimeUniversalPassedShiftMachine.start, none, 2)
        else if se = .final then
          (.final, none, 2)
        else
          let tr := runtimeProgressExhaustMachine.δ se b
          (.exhaust tr.1, tr.2.1, tr.2.2)
    | .final => (.final, none, 2)
  accept := fun s => decide (s = .final)

def outerShiftCfg (c : Cfg runtimeUniversalPassedShiftMachine) :
    Cfg runtimeFixedOuterControllerMachine :=
  ⟨.shift c.st, c.hd, c.tp⟩

def outerReturnCfg (c : Cfg runtimeProgressReturnMachine) :
    Cfg runtimeFixedOuterControllerMachine :=
  ⟨.ret c.st, c.hd, c.tp⟩

def outerExhaustCfg (c : Cfg runtimeProgressExhaustMachine) :
    Cfg runtimeFixedOuterControllerMachine :=
  ⟨.exhaust c.st, c.hd, c.tp⟩

theorem runtimeFixedOuterController_shift_step
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : runtimeUniversalPassedShiftMachine.halt c.st = false) :
    step runtimeFixedOuterControllerMachine (outerShiftCfg c) =
      outerShiftCfg (step runtimeUniversalPassedShiftMachine c) := by
  simp [step, runtimeFixedOuterControllerMachine, outerShiftCfg, h]

theorem runtimeFixedOuterController_shift_handoff
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : runtimeUniversalPassedShiftMachine.halt c.st = true) :
    step runtimeFixedOuterControllerMachine (outerShiftCfg c) =
      outerReturnCfg
        ⟨runtimeProgressReturnMachine.start, c.hd, c.tp⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, outerShiftCfg,
    outerReturnCfg, h, moveHead]

theorem runtimeFixedOuterController_return_step
    (c : Cfg runtimeProgressReturnMachine)
    (h : runtimeProgressReturnMachine.halt c.st = false) :
    step runtimeFixedOuterControllerMachine (outerReturnCfg c) =
      outerReturnCfg (step runtimeProgressReturnMachine c) := by
  simp [step, runtimeFixedOuterControllerMachine, outerReturnCfg, h]

theorem runtimeFixedOuterController_return_handoff
    (c : Cfg runtimeProgressReturnMachine)
    (h : runtimeProgressReturnMachine.halt c.st = true) :
    step runtimeFixedOuterControllerMachine (outerReturnCfg c) =
      outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start, c.hd, c.tp⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, outerReturnCfg,
    outerExhaustCfg, h, moveHead]

theorem runtimeFixedOuterController_exhaust_step
    (c : Cfg runtimeProgressExhaustMachine)
    (hm : c.st ≠ .more) (hf : c.st ≠ .final) :
    step runtimeFixedOuterControllerMachine (outerExhaustCfg c) =
      outerExhaustCfg (step runtimeProgressExhaustMachine c) := by
  have hh : runtimeProgressExhaustMachine.halt c.st = false := by
    simp [runtimeProgressExhaustMachine, hm, hf]
  simp [step, runtimeFixedOuterControllerMachine, outerExhaustCfg, hm, hf, hh]

/-- The physical `more` decision loops to the universal forward pass without
moving the head or changing tape. -/
theorem runtimeFixedOuterController_more_handoff
    (p : Nat) (T : List Bool) :
    step runtimeFixedOuterControllerMachine
        ⟨RuntimeFixedOuterControllerState.exhaust .more, p, T⟩ =
      ⟨runtimeFixedOuterControllerMachine.start, p, T⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, moveHead]

/-- The physical sentinel decision enters the sole genuine halt state,
again without moving the head or changing tape. -/
theorem runtimeFixedOuterController_final_handoff
    (p : Nat) (T : List Bool) :
    step runtimeFixedOuterControllerMachine
        ⟨RuntimeFixedOuterControllerState.exhaust .final, p, T⟩ =
      ⟨RuntimeFixedOuterControllerState.final, p, T⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, moveHead]

/-! ## Exact run lifting through the wrapper -/

theorem runtimeFixedOuterController_shift_run
    (c : Cfg runtimeUniversalPassedShiftMachine) (t : Nat)
    (hno : ∀ i < t, runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine i c).st = false) :
    run runtimeFixedOuterControllerMachine t (outerShiftCfg c) =
      outerShiftCfg (run runtimeUniversalPassedShiftMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedOuterController_shift_step _ (hno t (by omega)),
        ← run_succ]

theorem runtimeFixedOuterController_shift_run_handoff
    (c : Cfg runtimeUniversalPassedShiftMachine) (t : Nat)
    (hno : ∀ i < t, runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine i c).st = false)
    (hh : runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine t c).st = true) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerShiftCfg c) =
      outerReturnCfg
        ⟨runtimeProgressReturnMachine.start,
          (run runtimeUniversalPassedShiftMachine t c).hd,
          (run runtimeUniversalPassedShiftMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_shift_run c t hno,
    runtimeFixedOuterController_shift_handoff _ hh]

theorem runtimeFixedOuterController_return_run
    (c : Cfg runtimeProgressReturnMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i c).st = false) :
    run runtimeFixedOuterControllerMachine t (outerReturnCfg c) =
      outerReturnCfg (run runtimeProgressReturnMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedOuterController_return_step _ (hno t (by omega)),
        ← run_succ]

theorem runtimeFixedOuterController_return_run_handoff
    (c : Cfg runtimeProgressReturnMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i c).st = false)
    (hh : runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine t c).st = true) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerReturnCfg c) =
      outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start,
          (run runtimeProgressReturnMachine t c).hd,
          (run runtimeProgressReturnMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_return_run c t hno,
    runtimeFixedOuterController_return_handoff _ hh]

theorem runtimeFixedOuterController_exhaust_run
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final) :
    run runtimeFixedOuterControllerMachine t (outerExhaustCfg c) =
      outerExhaustCfg (run runtimeProgressExhaustMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedOuterController_exhaust_step _
          (hno t (by omega)).1 (hno t (by omega)).2,
        ← run_succ]

theorem runtimeFixedOuterController_exhaust_more_run_handoff
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final)
    (hm : (run runtimeProgressExhaustMachine t c).st = .more) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerExhaustCfg c) =
      ⟨runtimeFixedOuterControllerMachine.start,
        (run runtimeProgressExhaustMachine t c).hd,
        (run runtimeProgressExhaustMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_exhaust_run c t hno]
  cases hrun : run runtimeProgressExhaustMachine t c
  simp only [hrun] at hm ⊢
  subst hm
  exact runtimeFixedOuterController_more_handoff _ _

theorem runtimeFixedOuterController_exhaust_final_run_handoff
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final)
    (hf : (run runtimeProgressExhaustMachine t c).st = .final) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerExhaustCfg c) =
      ⟨RuntimeFixedOuterControllerState.final,
        (run runtimeProgressExhaustMachine t c).hd,
        (run runtimeProgressExhaustMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_exhaust_run c t hno]
  cases hrun : run runtimeProgressExhaustMachine t c
  simp only [hrun] at hf ⊢
  subst hf
  exact runtimeFixedOuterController_final_handoff _ _

/-! ## Concrete first-halt facts -/

/-- The two-step `more` test cannot reach either routing state early. -/
theorem runtimeProgressExhaust_more_no_early
    (pre tail : List Bool) :
    ∀ i < 2,
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩).st ≠ .final := by
  intro i hi
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressExhaustMachine, moveHead]

/-- The three-step sentinel test cannot reach either routing state early. -/
theorem runtimeProgressExhaust_final_no_early
    (pre tail : List Bool) :
    ∀ i < 3,
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [false, true, false, false] ++ tail⟩).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [false, true, false, false] ++ tail⟩).st ≠ .final := by
  intro i hi
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressExhaustMachine, moveHead,
      List.getD_eq_getElem?_getD, writeAt]

/-- The concrete `more` test, including its loop-back control transition,
lifts to one exact run of the fixed wrapper. -/
theorem runtimeFixedOuterController_exhaust_more_exact
    (pre tail : List Bool) :
    run runtimeFixedOuterControllerMachine 3
        (outerExhaustCfg
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
            pre ++ [true, false, false, false] ++ tail⟩) =
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩ := by
  have hr := runtimeProgressExhaust_more pre tail
  have hh : (run runtimeProgressExhaustMachine 2
      ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩).st = .more := by
    rw [hr]
  have h := runtimeFixedOuterController_exhaust_more_run_handoff
    _ 2 (runtimeProgressExhaust_more_no_early pre tail) hh
  rw [hr] at h
  simpa using h

/-- The concrete sentinel test, including the final pure-control transition,
lifts to an exact genuinely halted wrapper run. -/
theorem runtimeFixedOuterController_exhaust_final_exact
    (pre tail : List Bool) :
    run runtimeFixedOuterControllerMachine 4
        (outerExhaustCfg
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
            pre ++ [false, true, false, false] ++ tail⟩) =
      ⟨RuntimeFixedOuterControllerState.final, pre.length + 1,
        pre ++ [false, false, false, false] ++ tail⟩ := by
  have hr := runtimeProgressExhaust_final pre tail
  have hh : (run runtimeProgressExhaustMachine 3
      ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
        pre ++ [false, true, false, false] ++ tail⟩).st = .final := by
    rw [hr]
  have h := runtimeFixedOuterController_exhaust_final_run_handoff
    _ 3 (runtimeProgressExhaust_final_no_early pre tail) hh
  rw [hr] at h
  simpa using h

@[simp] theorem runtimeFixedOuterController_final_halts :
    runtimeFixedOuterControllerMachine.halt
      RuntimeFixedOuterControllerState.final = true := by
  simp [runtimeFixedOuterControllerMachine]

#print axioms runtimeFixedOuterController_shift_step
#print axioms runtimeFixedOuterController_shift_handoff
#print axioms runtimeFixedOuterController_return_step
#print axioms runtimeFixedOuterController_return_handoff
#print axioms runtimeFixedOuterController_exhaust_step
#print axioms runtimeFixedOuterController_more_handoff
#print axioms runtimeFixedOuterController_final_handoff
#print axioms runtimeFixedOuterController_shift_run_handoff
#print axioms runtimeFixedOuterController_return_run_handoff
#print axioms runtimeFixedOuterController_exhaust_more_run_handoff
#print axioms runtimeFixedOuterController_exhaust_final_run_handoff
#print axioms runtimeProgressExhaust_more_no_early
#print axioms runtimeProgressExhaust_final_no_early
#print axioms runtimeFixedOuterController_exhaust_more_exact
#print axioms runtimeFixedOuterController_exhaust_final_exact

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
