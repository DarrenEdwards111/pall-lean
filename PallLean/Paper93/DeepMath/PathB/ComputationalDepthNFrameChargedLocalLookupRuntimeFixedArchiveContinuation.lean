import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedCleanupRelocate

/-!
# Fixed cleanup, relocation, and archive-return continuation
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedArchiveContinuation

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupRelocate
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedContinuationRelocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

/-- One fixed controller through cleanup, physical relocation, and archive
return/seed installation. -/
def runtimeFixedArchiveContinuationMachine : Machine :=
  headSeqMachine runtimeFixedCleanupRelocateMachine
    runtimeArchiveReturnSeedMachine

def runtimeFixedArchiveContinuationDone :
    runtimeFixedArchiveContinuationMachine.State :=
  Sum.inr (Sum.inr RuntimeRebaseSeedState.done)

/-- Exact physical continuation through canonical archive seed installation.
The predecessor pair is discovered from the tape boundary contract. -/
theorem runtimeFixedArchiveContinuation_workspace
    (pre bits first : List Bool) (more : List (List Bool))
    (value : Bool) (m n : Nat) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let leftClock := runtimeFixedCleanupRelocateClock bits workspace.length clearClock
    let seedClock := runtimeArchiveReturnSeedClock (first :: more)
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
    let cleanedTape := pre ++ [false, false, false, false] ++
      flattenPairs (passedSourceBlock bits) ++
      flattenPairs (List.replicate workspace.length (false, false)) ++
      selectedTail (first :: more)
    let R := pre.length + 4 +
      2 * (passedSourceBlock bits ++
        List.replicate workspace.length (false, false)).length
    ∃ archivePre a b,
      archivePre.length = R - 2 ∧
      cleanedTape = archivePre ++ [a, b] ++ selectedTail (first :: more) ∧
      run runtimeFixedArchiveContinuationMachine
          (leftClock + 1 + seedClock)
          ⟨runtimeFixedArchiveContinuationMachine.start,
            pre.length, inputTape⟩ =
        ⟨runtimeFixedArchiveContinuationDone, R,
          archivePre ++ [false, true] ++ selectedTail (first :: more)⟩ := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let leftClock := runtimeFixedCleanupRelocateClock bits workspace.length clearClock
  let seedClock := runtimeArchiveReturnSeedClock (first :: more)
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
  let physicalPrefix := pre ++ [false, false, false, false] ++
    flattenPairs (passedSourceBlock bits) ++
    flattenPairs (List.replicate workspace.length (false, false))
  let cleanedTape := physicalPrefix ++ selectedTail (first :: more)
  let R := pre.length + 4 +
    2 * (passedSourceBlock bits ++
      List.replicate workspace.length (false, false)).length
  have hprefixLen : physicalPrefix.length = R := by
    simp [physicalPrefix, R, flattenPairs_length]
    omega
  have hR : 2 ≤ R := by
    simp [R, passedSourceBlock, workspace, runtimeWorkspaceFrontPairs]
    omega
  have hRlen : R ≤ cleanedTape.length := by
    simp [cleanedTape, hprefixLen]
  have hdrop : cleanedTape.drop R = selectedTail (first :: more) := by
    change (physicalPrefix ++ selectedTail (first :: more)).drop R = _
    rw [← hprefixLen]
    simp
  obtain ⟨archivePre, a, b, hpre, hshape, hseed⟩ :=
    runtimeArchiveReturnSeed_run_of_drop cleanedTape R first more
      hR hRlen hdrop
  refine ⟨archivePre, a, b, hpre, hshape, ?_⟩
  have hleft := runtimeFixedCleanupRelocate_workspace
    pre bits first more value m n
  have hleftHalt : runtimeFixedCleanupRelocateMachine.halt
      runtimeFixedCleanupRelocateDone = true := by
    simp [runtimeFixedCleanupRelocateMachine,
      runtimeFixedCleanupRelocateDone, headSeqMachine,
      runtimeFixedContinuationRelocatorMachine]
  have hseedHalt : runtimeArchiveReturnSeedMachine.halt
      (Sum.inr RuntimeRebaseSeedState.done) = true := by
    simp [runtimeArchiveReturnSeedMachine, headSeqMachine,
      runtimeRebaseSeedMachine]
  have hall := headSeq_run_at runtimeFixedCleanupRelocateMachine
    runtimeArchiveReturnSeedMachine inputTape cleanedTape
    (archivePre ++ [false, true] ++ selectedTail (first :: more))
    pre.length leftClock seedClock R R runtimeFixedCleanupRelocateDone
    (Sum.inr RuntimeRebaseSeedState.done)
    (by simpa [workspace, clearClock, leftClock, inputTape, cleanedTape,
      physicalPrefix, R, flattenPairs_append, List.append_assoc] using hleft)
    hleftHalt
    hseed
    hseedHalt
  simpa [runtimeFixedArchiveContinuationMachine,
    runtimeFixedArchiveContinuationDone, workspace, clearClock, leftClock,
    seedClock, inputTape, cleanedTape, physicalPrefix, R,
    flattenPairs_length, Nat.add_assoc, List.append_assoc] using hall

#print axioms runtimeFixedArchiveContinuation_workspace

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedArchiveContinuation
