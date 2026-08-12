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
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
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

theorem runtimeFixedCleanupController_clear_run
    (c : Cfg runtimeProgressRecordClearMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i c).st = false) :
    run runtimeFixedCleanupControllerMachine t (cleanupClearCfg c) =
      cleanupClearCfg (run runtimeProgressRecordClearMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedCleanupController_clear_step _ (hno t (by omega)),
        ← run_succ]

theorem runtimeFixedCleanupController_clear_run_handoff
    (c : Cfg runtimeProgressRecordClearMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i c).st = false)
    (hh : runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine t c).st = true) :
    run runtimeFixedCleanupControllerMachine (t + 1) (cleanupClearCfg c) =
      cleanupOuterCfg
        ⟨runtimeFixedOuterControllerMachine.start,
          (run runtimeProgressRecordClearMachine t c).hd,
          (run runtimeProgressRecordClearMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedCleanupController_clear_run c t hno,
    runtimeFixedCleanupController_clear_handoff _ hh]

theorem runtimeFixedCleanupController_clear_leftSafe
    (c : Cfg runtimeProgressRecordClearMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i c).st = false)
    (hsafe : LeftSafeRun runtimeProgressRecordClearMachine c t) :
    LeftSafeRun runtimeFixedCleanupControllerMachine (cleanupClearCfg c) t := by
  intro i hi hhalt hmove
  have hrun := runtimeFixedCleanupController_clear_run c i
    (fun j hj => hno j (by omega))
  rw [hrun] at hhalt hmove ⊢
  simp only [cleanupClearCfg] at hhalt hmove ⊢
  have hlocalHalt : runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine i c).st = false := hno i hi
  simp [runtimeFixedCleanupControllerMachine, hlocalHalt] at hmove
  exact hsafe i hi hlocalHalt hmove

theorem runtimeFixedCleanupController_clear_handoff_leftSafe
    (c : Cfg runtimeProgressRecordClearMachine)
    (hh : runtimeProgressRecordClearMachine.halt c.st = true) :
    LeftSafeRun runtimeFixedCleanupControllerMachine (cleanupClearCfg c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [runtimeFixedCleanupControllerMachine, cleanupClearCfg, hh]

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

theorem runtimeFixedCleanupController_outer_leftSafe
    (c : Cfg runtimeFixedOuterControllerMachine) (t : Nat)
    (hsafe : LeftSafeRun runtimeFixedOuterControllerMachine c t) :
    LeftSafeRun runtimeFixedCleanupControllerMachine (cleanupOuterCfg c) t := by
  intro i hi hhalt hmove
  rw [runtimeFixedCleanupController_outer_run] at hhalt hmove ⊢
  simp only [cleanupOuterCfg] at hhalt hmove ⊢
  have hlocalHalt : runtimeFixedOuterControllerMachine.halt
      (run runtimeFixedOuterControllerMachine i c).st = false := by
    simpa [runtimeFixedCleanupControllerMachine] using hhalt
  have hlocalMove : (runtimeFixedOuterControllerMachine.δ
      (run runtimeFixedOuterControllerMachine i c).st
      ((run runtimeFixedOuterControllerMachine i c).tp.getD
        (run runtimeFixedOuterControllerMachine i c).hd false)).2.2 = 0 := by
    simpa [runtimeFixedCleanupControllerMachine] using hmove
  exact hsafe i hi hlocalHalt hlocalMove

/-- The already-certified clear phase and its pure-control handoff are safe
as one prefix of the combined cleanup run. -/
theorem runtimeFixedCleanupController_workspace_clear_leftSafe
    (pre tail bits : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ tail
    LeftSafeRun runtimeFixedCleanupControllerMachine
      ⟨runtimeFixedCleanupControllerMachine.start, pre.length, inputTape⟩
      (clearClock + 1) := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ tail
  apply leftSafeRun_add
  · change LeftSafeRun runtimeFixedCleanupControllerMachine
      (cleanupClearCfg
        ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩)
      clearClock
    apply runtimeFixedCleanupController_clear_leftSafe
    · simpa [workspace, clearClock, inputTape, List.append_assoc] using
        runtimeProgressRecordClear_workspace_no_early pre
          (flattenPairs (passedSourceBlock bits) ++ tail) value m n
    · simpa [workspace, clearClock, inputTape, List.append_assoc] using
        runtimeProgressRecordClear_workspace_leftSafe pre
          (flattenPairs (passedSourceBlock bits) ++ tail) value m n
  · have hc := runtimeProgressRecordClear_workspace pre
      (flattenPairs (passedSourceBlock bits) ++ tail) value m n
    rw [show run runtimeFixedCleanupControllerMachine clearClock
        ⟨runtimeFixedCleanupControllerMachine.start, pre.length, inputTape⟩ =
        cleanupClearCfg
          ⟨RuntimeProgressRecordClearState.done,
            pre.length + 2 * workspace.length + 2,
            pre ++ [false, true] ++
              flattenPairs (List.replicate workspace.length (true, false)) ++
              [false, false] ++ flattenPairs (passedSourceBlock bits) ++ tail⟩ by
      change run runtimeFixedCleanupControllerMachine clearClock
          (cleanupClearCfg
            ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩) = _
      rw [runtimeFixedCleanupController_clear_run _ clearClock]
      · congr 1
        simpa [workspace, clearClock, inputTape, List.append_assoc] using hc
      · simpa [workspace, clearClock, inputTape, List.append_assoc] using
          runtimeProgressRecordClear_workspace_no_early pre
            (flattenPairs (passedSourceBlock bits) ++ tail) value m n]
    apply runtimeFixedCleanupController_clear_handoff_leftSafe
    simp [runtimeProgressRecordClearMachine]

/-- Complete exact cleanup run on a certified workspace followed immediately
by one self-delimiting passed block.  The fixed machine clears the workspace,
uses its physical progress words to shift the passed block left across the
entire span, clears the sentinel, and genuinely halts. -/
theorem runtimeFixedCleanupController_workspace
    (pre tail bits : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let outerClock := runtimeFixedOuterControllerRoundsClock bits workspace.length
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ tail
    let outputTape := pre ++ [false, false, false, false] ++
      flattenPairs (passedSourceBlock bits) ++
      flattenPairs (List.replicate workspace.length (false, false)) ++ tail
    run runtimeFixedCleanupControllerMachine
        ((clearClock + 1) + outerClock)
        ⟨runtimeFixedCleanupControllerMachine.start, pre.length, inputTape⟩ =
      ⟨RuntimeFixedCleanupControllerState.outer
          RuntimeFixedOuterControllerState.final,
        pre.length + 1, outputTape⟩ := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ tail
  let recordTape := pre ++ [false, true] ++
    flattenPairs (List.replicate workspace.length (true, false)) ++
    [false, false] ++ flattenPairs (passedSourceBlock bits) ++ tail
  rw [run_add]
  have hcExact := runtimeProgressRecordClear_workspace pre
    (flattenPairs (passedSourceBlock bits) ++ tail) value m n
  have hcNoEarly := runtimeProgressRecordClear_workspace_no_early pre
    (flattenPairs (passedSourceBlock bits) ++ tail) value m n
  have hcHalt : runtimeProgressRecordClearMachine.halt
      (run runtimeProgressRecordClearMachine clearClock
        ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩).st = true := by
    rw [show run runtimeProgressRecordClearMachine clearClock
        ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩ =
        ⟨RuntimeProgressRecordClearState.done,
          pre.length + 2 * workspace.length + 2, recordTape⟩ by
      simpa [workspace, clearClock, inputTape, recordTape,
        List.append_assoc] using hcExact]
    simp [runtimeProgressRecordClearMachine]
  have hc := runtimeFixedCleanupController_clear_run_handoff
    ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩
    clearClock
    (by simpa [workspace, clearClock, inputTape, List.append_assoc] using hcNoEarly)
    hcHalt
  rw [show run runtimeFixedCleanupControllerMachine (clearClock + 1)
      ⟨runtimeFixedCleanupControllerMachine.start, pre.length, inputTape⟩ =
      cleanupOuterCfg
        ⟨runtimeFixedOuterControllerMachine.start,
          pre.length + 2 * workspace.length + 2, recordTape⟩ by
    change run runtimeFixedCleanupControllerMachine (clearClock + 1)
        (cleanupClearCfg
          ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩) = _
    rw [hc]
    rw [show run runtimeProgressRecordClearMachine clearClock
        ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩ =
        ⟨RuntimeProgressRecordClearState.done,
          pre.length + 2 * workspace.length + 2, recordTape⟩ by
      simpa [workspace, clearClock, inputTape, recordTape,
        List.append_assoc] using hcExact]]
  rw [runtimeFixedCleanupController_outer_run]
  have ho := runtimeFixedOuterController_rounds pre tail bits
    (workspace.length - 1)
  have hwpos : 0 < workspace.length := by
    simp [workspace, runtimeWorkspaceFrontPairs]
  have hpred : workspace.length - 1 + 1 = workspace.length := by omega
  rw [hpred] at ho
  rw [show run runtimeFixedOuterControllerMachine
      (runtimeFixedOuterControllerRoundsClock bits workspace.length)
      ⟨runtimeFixedOuterControllerMachine.start,
        pre.length + 2 * workspace.length + 2, recordTape⟩ =
      ⟨RuntimeFixedOuterControllerState.final, pre.length + 1,
        pre ++ [false, false, false, false] ++
          flattenPairs (passedSourceBlock bits) ++
          flattenPairs (List.replicate workspace.length (false, false)) ++ tail⟩ by
    simpa [recordTape, workspace, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ho]
  rfl

/-- Matching left-boundary certificate for the complete exact cleanup run. -/
theorem runtimeFixedCleanupController_workspace_leftSafe
    (pre tail bits : List Bool) (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let outerClock := runtimeFixedOuterControllerRoundsClock bits workspace.length
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ tail
    LeftSafeRun runtimeFixedCleanupControllerMachine
      ⟨runtimeFixedCleanupControllerMachine.start, pre.length, inputTape⟩
      ((clearClock + 1) + outerClock) := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ tail
  let recordTape := pre ++ [false, true] ++
    flattenPairs (List.replicate workspace.length (true, false)) ++
    [false, false] ++ flattenPairs (passedSourceBlock bits) ++ tail
  apply leftSafeRun_add
  · simpa [workspace, clearClock, inputTape] using
      runtimeFixedCleanupController_workspace_clear_leftSafe
        pre tail bits value m n
  · have hcExact := runtimeProgressRecordClear_workspace pre
      (flattenPairs (passedSourceBlock bits) ++ tail) value m n
    have hcNoEarly := runtimeProgressRecordClear_workspace_no_early pre
      (flattenPairs (passedSourceBlock bits) ++ tail) value m n
    have hcHalt : runtimeProgressRecordClearMachine.halt
        (run runtimeProgressRecordClearMachine clearClock
          ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩).st = true := by
      rw [show run runtimeProgressRecordClearMachine clearClock
          ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩ =
          ⟨RuntimeProgressRecordClearState.done,
            pre.length + 2 * workspace.length + 2, recordTape⟩ by
        simpa [workspace, clearClock, inputTape, recordTape,
          List.append_assoc] using hcExact]
      simp [runtimeProgressRecordClearMachine]
    have hc := runtimeFixedCleanupController_clear_run_handoff
      ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩
      clearClock
      (by simpa [workspace, clearClock, inputTape, List.append_assoc] using hcNoEarly)
      hcHalt
    rw [show run runtimeFixedCleanupControllerMachine (clearClock + 1)
        ⟨runtimeFixedCleanupControllerMachine.start, pre.length, inputTape⟩ =
        cleanupOuterCfg
          ⟨runtimeFixedOuterControllerMachine.start,
            pre.length + 2 * workspace.length + 2, recordTape⟩ by
      change run runtimeFixedCleanupControllerMachine (clearClock + 1)
          (cleanupClearCfg
            ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩) = _
      rw [hc]
      rw [show run runtimeProgressRecordClearMachine clearClock
          ⟨runtimeProgressRecordClearMachine.start, pre.length, inputTape⟩ =
          ⟨RuntimeProgressRecordClearState.done,
            pre.length + 2 * workspace.length + 2, recordTape⟩ by
        simpa [workspace, clearClock, inputTape, recordTape,
          List.append_assoc] using hcExact]]
    apply runtimeFixedCleanupController_outer_leftSafe
    have hwpos : 0 < workspace.length := by
      simp [workspace, runtimeWorkspaceFrontPairs]
    have ho := runtimeFixedOuterController_rounds_leftSafe pre tail bits
      (workspace.length - 1)
    have hpred : workspace.length - 1 + 1 = workspace.length := by omega
    rw [hpred] at ho
    simpa [recordTape, workspace, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ho

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
#print axioms runtimeFixedCleanupController_clear_run_handoff
#print axioms runtimeFixedCleanupController_clear_leftSafe
#print axioms runtimeFixedCleanupController_outer_leftSafe
#print axioms runtimeFixedCleanupController_workspace_clear_leftSafe
#print axioms runtimeFixedCleanupController_workspace
#print axioms runtimeFixedCleanupController_workspace_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupController
