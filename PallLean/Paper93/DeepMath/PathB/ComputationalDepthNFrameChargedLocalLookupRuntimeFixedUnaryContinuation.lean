import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedArchiveContinuation

/-!
# Complete fixed cleanup-to-unary continuation
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedUnaryContinuation

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupRelocate
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedArchiveContinuation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

/-- The complete fixed controller through physical unary rebase. -/
def runtimeFixedUnaryContinuationMachine : Machine :=
  headSeqMachine runtimeFixedArchiveContinuationMachine
    runtimeUnaryRebaseMachine

def runtimeFixedUnaryContinuationDone :
    runtimeFixedUnaryContinuationMachine.State :=
  Sum.inr RuntimeUnaryRebaseState.done

/-- Exact complete fixed continuation and matching safety.  The only numeric
premise is the physical scratch-capacity inequality required by the unary
writer; it does not enter finite control. -/
theorem runtimeFixedUnaryContinuation_workspace
    (pre bits first : List Bool) (more : List (List Bool))
    (value : Bool) (m n : Nat)
    (hfit :
      2 * (first :: more).length + 4 ≤
        pre.length + 2 +
          2 * (passedSourceBlock bits ++
            List.replicate
              (runtimeWorkspaceFrontPairs value m n).length
              (false, false)).length) :
    let workspace := runtimeWorkspaceFrontPairs value m n
    let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
    let archiveClock :=
      runtimeFixedCleanupRelocateClock bits workspace.length clearClock + 1 +
        runtimeArchiveReturnSeedClock (first :: more)
    let inputTape := pre ++ flattenPairs workspace ++
      flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
    ∃ phys base unaryClock,
      phys.length = pre.length + 2 +
        2 * (passedSourceBlock bits ++
          List.replicate workspace.length (false, false)).length ∧
      base.IsPrefix phys ∧
      base.length = phys.length - (2 * (first :: more).length + 4) ∧
      run runtimeFixedUnaryContinuationMachine
          (archiveClock + 1 + unaryClock)
          ⟨runtimeFixedUnaryContinuationMachine.start,
            pre.length, inputTape⟩ =
        ⟨runtimeFixedUnaryContinuationDone,
          phys.length + 2 + (selectedTail (first :: more)).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput (first :: more).length 0 (first :: more)⟩ ∧
      LeftSafeRun runtimeFixedUnaryContinuationMachine
        ⟨runtimeFixedUnaryContinuationMachine.start,
          pre.length, inputTape⟩
        (archiveClock + 1 + unaryClock) := by
  dsimp only
  let workspace := runtimeWorkspaceFrontPairs value m n
  let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
  let archiveClock :=
    runtimeFixedCleanupRelocateClock bits workspace.length clearClock + 1 +
      runtimeArchiveReturnSeedClock (first :: more)
  let inputTape := pre ++ flattenPairs workspace ++
    flattenPairs runtimePassedBoundaryMarker ++
    flattenPairs (passedSourceBlock bits) ++ selectedTail (first :: more)
  obtain ⟨phys, a, b, hphysLen, hshape, harchive⟩ :=
    runtimeFixedArchiveContinuation_workspace pre bits first more value m n
  have hphysLen' : phys.length = pre.length + 2 +
      2 * (passedSourceBlock bits ++
        List.replicate workspace.length (false, false)).length := by
    rw [hphysLen]
    simp [workspace]
    omega
  have hfit' : 2 * (first :: more).length + 4 ≤ phys.length := by
    rw [hphysLen']
    simpa [workspace] using hfit
  obtain ⟨base, unaryClock, hbasePrefix, hbaseLen, hunary, hunarySafe⟩ :=
    runtimeUnaryRebase_physical_safeRun phys first more hfit'
  have harchive' : run runtimeFixedArchiveContinuationMachine archiveClock
      ⟨runtimeFixedArchiveContinuationMachine.start,
        pre.length, inputTape⟩ =
    ⟨runtimeFixedArchiveContinuationDone, phys.length + 2,
      phys ++ [false, true] ++ selectedTail (first :: more)⟩ := by
    convert harchive using 1
    all_goals simp [workspace, hphysLen', Nat.add_assoc, List.append_assoc]
    all_goals try omega
  refine ⟨phys, base, unaryClock, hphysLen', hbasePrefix, hbaseLen, ?_, ?_⟩
  · have harchiveHalt : runtimeFixedArchiveContinuationMachine.halt
        runtimeFixedArchiveContinuationDone = true := by
      simp [runtimeFixedArchiveContinuationMachine,
        runtimeFixedArchiveContinuationDone, headSeqMachine,
        runtimeArchiveReturnSeedMachine, runtimeRebaseSeedMachine]
    have hunaryHalt : runtimeUnaryRebaseMachine.halt
        RuntimeUnaryRebaseState.done = true := by
      simp [runtimeUnaryRebaseMachine]
    have hall := headSeq_run_at runtimeFixedArchiveContinuationMachine
      runtimeUnaryRebaseMachine inputTape
      (phys ++ [false, true] ++ selectedTail (first :: more))
      (base ++ [false, true, false, true] ++
        sourceSelectorInput (first :: more).length 0 (first :: more))
      pre.length archiveClock unaryClock (phys.length + 2)
      (phys.length + 2 + (selectedTail (first :: more)).length)
      runtimeFixedArchiveContinuationDone RuntimeUnaryRebaseState.done
      harchive'
      harchiveHalt
      hunary
      hunaryHalt
    simpa [runtimeFixedUnaryContinuationMachine,
      runtimeFixedUnaryContinuationDone, workspace, clearClock,
      archiveClock, inputTape, Nat.add_assoc] using hall
  · have harchiveSafe :=
      runtimeFixedArchiveContinuation_workspace_leftSafe
        pre bits first more value m n
    have harchiveHalt : runtimeFixedArchiveContinuationMachine.halt
        runtimeFixedArchiveContinuationDone = true := by
      simp [runtimeFixedArchiveContinuationMachine,
        runtimeFixedArchiveContinuationDone, headSeqMachine,
        runtimeArchiveReturnSeedMachine, runtimeRebaseSeedMachine]
    have hunaryHalt : runtimeUnaryRebaseMachine.halt
        (run runtimeUnaryRebaseMachine unaryClock
          ⟨runtimeUnaryRebaseMachine.start, phys.length + 2,
            phys ++ [false, true] ++ selectedTail (first :: more)⟩).st = true := by
      change runtimeUnaryRebaseMachine.halt
        (run runtimeUnaryRebaseMachine unaryClock
          ⟨RuntimeUnaryRebaseState.init1, phys.length + 2,
            phys ++ [false, true] ++ selectedTail (first :: more)⟩).st = true
      rw [hunary]
      simp [runtimeUnaryRebaseMachine]
    have hs := headSeq_leftSafe_at runtimeFixedArchiveContinuationMachine
      runtimeUnaryRebaseMachine inputTape
      (phys ++ [false, true] ++ selectedTail (first :: more))
      pre.length archiveClock unaryClock (phys.length + 2)
      runtimeFixedArchiveContinuationDone
      harchive'
      harchiveHalt
      (by simpa [workspace, clearClock, archiveClock, inputTape,
        Nat.add_assoc] using harchiveSafe)
      hunarySafe
      hunaryHalt
    simpa [runtimeFixedUnaryContinuationMachine, workspace, clearClock,
      archiveClock, inputTape, Nat.add_assoc] using hs

#print axioms runtimeFixedUnaryContinuation_workspace

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedUnaryContinuation
