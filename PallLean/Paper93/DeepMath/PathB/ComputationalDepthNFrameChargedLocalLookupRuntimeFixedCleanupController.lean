import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedOuterController
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeProgressRecordClear

/-!
# One fixed controller for progress clearing and passed-block compaction

This is the final physical wrapper for the cleanup protocol.  Its finite
control contains only the fixed progress-record clearer and fixed outer-loop
controller.  When the clearer genuinely halts on the initial hole, one
tape-preserving control transition starts the universal outer controller.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupController

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressRecordClear
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController

inductive RuntimeFixedCleanupControllerState
  | clear (s : RuntimeProgressRecordClearState)
  | outer (s : RuntimeFixedOuterControllerState)
  deriving DecidableEq, Fintype

/-- One constant finite-state cleanup controller.  No input value, workspace
length, payload length, schedule, offset, or round number occurs in its state. -/
def runtimeFixedCleanupControllerMachine : Machine where
  State := RuntimeFixedCleanupControllerState
  fin := inferInstance
  dec := inferInstance
  start := .clear runtimeProgressRecordClearMachine.start
  halt := fun s =>
    match s with
    | .clear _ => false
    | .outer so => runtimeFixedOuterControllerMachine.halt so
  δ := fun s b =>
    match s with
    | .clear sc =>
        if runtimeProgressRecordClearMachine.halt sc then
          (.outer runtimeFixedOuterControllerMachine.start, none, 2)
        else
          let tr := runtimeProgressRecordClearMachine.δ sc b
          (.clear tr.1, tr.2.1, tr.2.2)
    | .outer so =>
        let tr := runtimeFixedOuterControllerMachine.δ so b
        (.outer tr.1, tr.2.1, tr.2.2)
  accept := fun s =>
    match s with
    | .clear _ => false
    | .outer so => runtimeFixedOuterControllerMachine.accept so

def cleanupClearCfg (c : Cfg runtimeProgressRecordClearMachine) :
    Cfg runtimeFixedCleanupControllerMachine :=
  ⟨.clear c.st, c.hd, c.tp⟩

def cleanupOuterCfg (c : Cfg runtimeFixedOuterControllerMachine) :
    Cfg runtimeFixedCleanupControllerMachine :=
  ⟨.outer c.st, c.hd, c.tp⟩

/-- Every nonhalting clearer transition is faithfully embedded. -/
theorem runtimeFixedCleanupController_clear_step
    (c : Cfg runtimeProgressRecordClearMachine)
    (h : runtimeProgressRecordClearMachine.halt c.st = false) :
    step runtimeFixedCleanupControllerMachine (cleanupClearCfg c) =
      cleanupClearCfg (step runtimeProgressRecordClearMachine c) := by
  simp [step, runtimeFixedCleanupControllerMachine, cleanupClearCfg, h]

/-- A genuinely halted clearer hands its exact head and tape to the fixed
outer controller in one pure-control transition. -/
theorem runtimeFixedCleanupController_clear_handoff
    (c : Cfg runtimeProgressRecordClearMachine)
    (h : runtimeProgressRecordClearMachine.halt c.st = true) :
    step runtimeFixedCleanupControllerMachine (cleanupClearCfg c) =
      cleanupOuterCfg
        ⟨runtimeFixedOuterControllerMachine.start, c.hd, c.tp⟩ := by
  simp [step, runtimeFixedCleanupControllerMachine, cleanupClearCfg,
    cleanupOuterCfg, h, moveHead]

/-- Every outer-controller transition is faithfully embedded, including its
sole final self-loop. -/
theorem runtimeFixedCleanupController_outer_step
    (c : Cfg runtimeFixedOuterControllerMachine) :
    step runtimeFixedCleanupControllerMachine (cleanupOuterCfg c) =
      cleanupOuterCfg (step runtimeFixedOuterControllerMachine c) := by
  rcases c with ⟨st, hd, tp⟩
  cases st <;>
    simp [step, runtimeFixedCleanupControllerMachine, cleanupOuterCfg,
      runtimeFixedOuterControllerMachine, moveHead]

/-- Arbitrary outer-controller runs lift without any timing side condition. -/
theorem runtimeFixedCleanupController_outer_run
    (c : Cfg runtimeFixedOuterControllerMachine) (t : Nat) :
    run runtimeFixedCleanupControllerMachine t (cleanupOuterCfg c) =
      cleanupOuterCfg (run runtimeFixedOuterControllerMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih, runtimeFixedCleanupController_outer_step, ← run_succ]

@[simp] theorem runtimeFixedCleanupController_outer_final_halts :
    runtimeFixedCleanupControllerMachine.halt
      (.outer RuntimeFixedOuterControllerState.final) = true := by
  simp [runtimeFixedCleanupControllerMachine,
    runtimeFixedOuterControllerMachine]

@[simp] theorem runtimeFixedCleanupController_clear_never_halts
    (s : RuntimeProgressRecordClearState) :
    runtimeFixedCleanupControllerMachine.halt (.clear s) = false := by
  rfl

#print axioms runtimeFixedCleanupController_clear_step
#print axioms runtimeFixedCleanupController_clear_handoff
#print axioms runtimeFixedCleanupController_outer_step
#print axioms runtimeFixedCleanupController_outer_run

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupController
