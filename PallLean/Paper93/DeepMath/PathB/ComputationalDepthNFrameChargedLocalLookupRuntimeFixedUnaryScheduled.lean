import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedUnaryContinuation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalUnaryRebase

/-!
# Scheduled specialization of the complete fixed unary continuation
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedUnaryScheduled

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupRelocate
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedUnaryContinuation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

set_option maxHeartbeats 2000000 in
/-- On every scheduled nonterminal round, the single fixed controller runs
from the genuine `masterM` endpoint through cleanup, continuation relocation,
archive return, and unary rebase. -/
theorem scheduled_runtimeFixedUnaryContinuation_run
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out' := (scheduledTruths x w).take (t + 1)
    let retained := outputCap B out' ++ pre
    let trailer := markedPreservedPassedTrailer bits (selectedTail rest)
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    retained ++ flattenPairs (passedSourceBlock bits) =
      outputCap B out' ++
        selectedPrefix (B - (t + 1)) (schedule.take (t + 1)) ∧
    ∃ value first more base unaryClock,
      rest = first :: more ∧
      let workspace := runtimeWorkspaceFrontPairs value
        (2 * l.1 + 2) (2 * l.1 + 4)
      let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
      let archiveClock :=
        runtimeFixedCleanupRelocateClock bits workspace.length clearClock + 1 +
          runtimeArchiveReturnSeedClock rest
      let inputTape := retained ++ cf.tp
      run runtimeFixedUnaryContinuationMachine
          (archiveClock + 1 + unaryClock)
          ⟨runtimeFixedUnaryContinuationMachine.start,
            retained.length, inputTape⟩ =
        ⟨runtimeFixedUnaryContinuationDone,
          (retained.length + 2 +
              2 * (passedSourceBlock bits ++
                List.replicate workspace.length (false, false)).length) + 2 +
            (selectedTail rest).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      LeftSafeRun runtimeFixedUnaryContinuationMachine
        ⟨runtimeFixedUnaryContinuationMachine.start,
          retained.length, inputTape⟩
        (archiveClock + 1 + unaryClock) := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out' := (scheduledTruths x w).take (t + 1)
  let retained := outputCap B out' ++ pre
  let trailer := markedPreservedPassedTrailer bits (selectedTail rest)
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hcanonical := scheduled_selectedPrefix_succ x w ht
  have hprefix : retained ++ flattenPairs (passedSourceBlock bits) =
      outputCap B out' ++
        selectedPrefix (B - (t + 1)) (schedule.take (t + 1)) := by
    simpa [retained, pre, B, schedule, preBlocks, bits, out',
      List.append_assoc] using congrArg (fun z => outputCap B out' ++ z)
        hcanonical.symm
  refine ⟨hprefix, ?_⟩
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hrestlen : rest.length = B - (t + 1) := by
    simp [rest, hslen]
  have hrestpos : 0 < rest.length := by omega
  obtain ⟨first, more, hrest⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hrestpos)
  obtain ⟨value, hcf⟩ :=
    masterM_literal_workspace_markedPassed_decomposition w l
      (selectedTail rest)
  let workspace := runtimeWorkspaceFrontPairs value
    (2 * l.1 + 2) (2 * l.1 + 4)
  have hfit0 := scheduled_unaryRebaseScratch_fits_afterOutput x w ht
  have hfit : 2 * rest.length + 4 ≤ retained.length + 2 +
      2 * (passedSourceBlock bits ++
        List.replicate workspace.length (false, false)).length := by
    have hp : pre.length + 2 * bits.length + 2 ≤
        retained.length + 2 +
          2 * (passedSourceBlock bits ++
            List.replicate workspace.length (false, false)).length := by
      simp [retained, workspace, passedSourceBlock, dataPairs]
      omega
    exact le_trans (by simpa [B, schedule, preBlocks, bits, rest, pre] using hfit0) hp
  have hfull := runtimeFixedUnaryContinuation_workspace retained bits
    first more value (2 * l.1 + 2) (2 * l.1 + 4)
    (by simpa [hrest] using hfit)
  obtain ⟨phys, base, unaryClock, hphys, hbase, hbaseLen, hrun, hsafe⟩ := hfull
  have hcf' : cf.tp =
      flattenPairs workspace ++
        flattenPairs runtimePassedBoundaryMarker ++
        flattenPairs (passedSourceBlock bits) ++ selectedTail rest := by
    simpa [cf, trailer, bits, workspace] using hcf
  have hinput : retained ++ cf.tp =
      retained ++ flattenPairs workspace ++
        flattenPairs runtimePassedBoundaryMarker ++
        flattenPairs (passedSourceBlock bits) ++ selectedTail rest := by
    rw [hcf']
    simp [List.append_assoc]
  have hrun' := hrun
  have hsafe' := hsafe
  rw [← hrest] at hrun' hsafe'
  rw [← hinput] at hrun' hsafe'
  refine ⟨value, first, more, base, unaryClock, hrest, ?_, ?_⟩
  · simpa [workspace, retained, bits, trailer, cf, rest, hrestlen, hphys,
      B, schedule, preBlocks, l, pre, out', List.append_assoc,
      Nat.add_assoc] using hrun'
  · simpa [workspace, retained, bits, trailer, cf, rest,
      B, schedule, preBlocks, l, pre, out', List.append_assoc,
      Nat.add_assoc] using hsafe'

#print axioms scheduled_runtimeFixedUnaryContinuation_run

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedUnaryScheduled
