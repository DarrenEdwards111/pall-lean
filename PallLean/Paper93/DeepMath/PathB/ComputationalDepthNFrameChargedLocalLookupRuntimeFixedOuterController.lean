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

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
