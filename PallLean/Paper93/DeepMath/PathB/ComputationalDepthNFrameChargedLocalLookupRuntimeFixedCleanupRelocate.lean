import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedContinuationRelocator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalLeftSafety

/-!
# One fixed controller for cleanup followed by continuation relocation

This wrapper joins the complete constant-state cleanup controller to the
constant-state continuation relocator with one head-preserving handoff.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupRelocate

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedContinuationRelocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

/-- One fixed finite controller for both cleanup and physical relocation. -/
def runtimeFixedCleanupRelocateMachine : Machine :=
  headSeqMachine runtimeFixedCleanupControllerMachine
    runtimeFixedContinuationRelocatorMachine

def runtimeFixedCleanupRelocateDone :
    runtimeFixedCleanupRelocateMachine.State :=
  Sum.inr RuntimeFixedContinuationRelocatorState.done

def runtimeFixedCleanupRelocateClock
    (bits : List Bool) (workspaceLength : Nat) (clearClock : Nat) : Nat :=
  ((clearClock + 1) +
      runtimeFixedOuterControllerRoundsClock bits workspaceLength) + 1 +
    runtimeFixedContinuationRelocatorClock bits workspaceLength

/-- Exact combined run.  The endpoint is precisely the low cell of the first
fresh archive header, ready for `runtimeArchiveReturnSeedMachine`. -/
theorem runtimeFixedCleanupRelocate_workspace
    (pre bits first : List Bool) (more : List (List Bool))
    (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
    let outputTape := pre ++ [false, false, false, false] ++
      flattenPairs (passedSourceBlock bits) ++
      flattenPairs (List.replicate workspace.length (false, false)) ++
      selectedTail (first :: more)
    run runtimeFixedCleanupRelocateMachine
        (runtimeFixedCleanupRelocateClock bits workspace.length clearClock)
        ⟨runtimeFixedCleanupRelocateMachine.start, pre.length, inputTape⟩ =
      ⟨runtimeFixedCleanupRelocateDone,
        pre.length + 4 +
          2 * (passedSourceBlock bits ++
            List.replicate workspace.length (false, false)).length,
        outputTape⟩ := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let cleanupClock := (clearClock + 1) +
    runtimeFixedOuterControllerRoundsClock bits workspace.length
  let relocateClock := runtimeFixedContinuationRelocatorClock bits workspace.length
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
  let outputTape := pre ++ [false, false, false, false] ++
    flattenPairs (passedSourceBlock bits) ++
    flattenPairs (List.replicate workspace.length (false, false)) ++
    selectedTail (first :: more)
  have hc := runtimeFixedCleanupController_workspace pre
    (selectedTail (first :: more)) bits value m n
  have hchalt : runtimeFixedCleanupControllerMachine.halt
      (RuntimeFixedCleanupControllerState.outer
        RuntimeFixedOuterControllerState.final) = true := by simp
  have hr := runtimeFixedContinuationRelocator_passed_holes
    pre bits first more workspace.length
  have hrhalt : runtimeFixedContinuationRelocatorMachine.halt
      RuntimeFixedContinuationRelocatorState.done = true := by
    simp [runtimeFixedContinuationRelocatorMachine]
  have hrun := headSeq_run_at runtimeFixedCleanupControllerMachine
    runtimeFixedContinuationRelocatorMachine inputTape outputTape outputTape
    pre.length cleanupClock relocateClock (pre.length + 1)
    (pre.length + 4 + 2 *
      (passedSourceBlock bits ++
        List.replicate workspace.length (false, false)).length)
    (RuntimeFixedCleanupControllerState.outer
      RuntimeFixedOuterControllerState.final)
    RuntimeFixedContinuationRelocatorState.done
    (by simpa [workspace, clearClock, cleanupClock, inputTape, outputTape,
      List.append_assoc] using hc)
    hchalt
    (by simpa [workspace, outputTape, relocateClock, flattenPairs_append,
      List.append_assoc] using hr)
    hrhalt
  simpa [runtimeFixedCleanupRelocateMachine,
    runtimeFixedCleanupRelocateDone, runtimeFixedCleanupRelocateClock,
    workspace, clearClock, cleanupClock, relocateClock, inputTape, outputTape,
    Nat.add_assoc] using hrun

/-- Matching safety certificate for the same complete wrapper run. -/
theorem runtimeFixedCleanupRelocate_workspace_leftSafe
    (pre bits first : List Bool) (more : List (List Bool))
    (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
    LeftSafeRun runtimeFixedCleanupRelocateMachine
      ⟨runtimeFixedCleanupRelocateMachine.start, pre.length, inputTape⟩
      (runtimeFixedCleanupRelocateClock bits workspace.length clearClock) := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let cleanupClock := (clearClock + 1) +
    runtimeFixedOuterControllerRoundsClock bits workspace.length
  let relocateClock := runtimeFixedContinuationRelocatorClock bits workspace.length
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
  let outputTape := pre ++ [false, false, false, false] ++
    flattenPairs (passedSourceBlock bits) ++
    flattenPairs (List.replicate workspace.length (false, false)) ++
    selectedTail (first :: more)
  have hc := runtimeFixedCleanupController_workspace pre
    (selectedTail (first :: more)) bits value m n
  have hchalt : runtimeFixedCleanupControllerMachine.halt
      (RuntimeFixedCleanupControllerState.outer
        RuntimeFixedOuterControllerState.final) = true := by simp
  have hcsafe := runtimeFixedCleanupController_workspace_leftSafe pre
    (selectedTail (first :: more)) bits value m n
  have hrsafe := runtimeFixedContinuationRelocator_passed_holes_leftSafe
    pre bits first more workspace.length
  have hr := runtimeFixedContinuationRelocator_passed_holes
    pre bits first more workspace.length
  have hrhalt : runtimeFixedContinuationRelocatorMachine.halt
      (run runtimeFixedContinuationRelocatorMachine relocateClock
        ⟨runtimeFixedContinuationRelocatorMachine.start,
          pre.length + 1, outputTape⟩).st = true := by
    rw [show run runtimeFixedContinuationRelocatorMachine relocateClock
        ⟨runtimeFixedContinuationRelocatorMachine.start,
          pre.length + 1, outputTape⟩ =
      ⟨RuntimeFixedContinuationRelocatorState.done,
        pre.length + 4 + 2 *
          (passedSourceBlock bits ++
            List.replicate workspace.length (false, false)).length,
        outputTape⟩ by
      simpa [workspace, outputTape, relocateClock, flattenPairs_append,
        List.append_assoc] using hr]
    simp [runtimeFixedContinuationRelocatorMachine]
  have hs := headSeq_leftSafe_at runtimeFixedCleanupControllerMachine
    runtimeFixedContinuationRelocatorMachine inputTape outputTape pre.length
    cleanupClock relocateClock (pre.length + 1)
    (RuntimeFixedCleanupControllerState.outer
      RuntimeFixedOuterControllerState.final)
    (by simpa [workspace, clearClock, cleanupClock, inputTape, outputTape,
      List.append_assoc] using hc)
    hchalt
    (by simpa [workspace, clearClock, cleanupClock, inputTape,
      List.append_assoc] using hcsafe)
    (by simpa [workspace, outputTape, relocateClock, flattenPairs_append,
      List.append_assoc] using hrsafe)
    hrhalt
  simpa [runtimeFixedCleanupRelocateMachine,
    runtimeFixedCleanupRelocateClock, workspace, clearClock, cleanupClock,
    relocateClock, inputTape, outputTape, Nat.add_assoc] using hs

#print axioms runtimeFixedCleanupRelocate_workspace
#print axioms runtimeFixedCleanupRelocate_workspace_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupRelocate
