import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedCleanupController
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundTransition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeStage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeSourceCompact

/-!
# Scheduled integration of the fixed cleanup controller

This module plugs the constant-state cleanup machine into the genuine
completed `masterM` layout with its preserved marked passed copy.  It replaces
the old translation/length-indexed compaction seam at this boundary.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupScheduled

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition

/-- From the genuine completed lookup tape, the one fixed cleanup controller
clears the workspace/marker prefix, shifts the preserved canonical passed
block fully left, genuinely halts, and satisfies the matching left-boundary
certificate. -/
theorem masterM_literal_fixedCleanup
    (retained tail w : List Bool) (l : Lit) :
    let bits := literalLookupTape w l
    let trailer := markedPreservedPassedTrailer bits tail
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let m := 2 * l.1 + 2
    let n := 2 * l.1 + 4
    ∃ value,
      let workspace := runtimeWorkspaceFrontPairs value m n
      let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
      let outerClock := runtimeFixedOuterControllerRoundsClock bits workspace.length
      let clock := (clearClock + 1) + outerClock
      let inputTape := retained ++ cf.tp
      let outputTape := retained ++ [false, false, false, false] ++
        flattenPairs (passedSourceBlock bits) ++
        flattenPairs (List.replicate workspace.length (false, false)) ++ tail
      run runtimeFixedCleanupControllerMachine clock
          ⟨runtimeFixedCleanupControllerMachine.start,
            retained.length, inputTape⟩ =
        ⟨RuntimeFixedCleanupControllerState.outer
            RuntimeFixedOuterControllerState.final,
          retained.length + 1, outputTape⟩ ∧
      runtimeFixedCleanupControllerMachine.halt
        (RuntimeFixedCleanupControllerState.outer
          RuntimeFixedOuterControllerState.final) = true ∧
      LeftSafeRun runtimeFixedCleanupControllerMachine
        ⟨runtimeFixedCleanupControllerMachine.start,
          retained.length, inputTape⟩ clock := by
  dsimp only
  let bits := literalLookupTape w l
  let trailer := markedPreservedPassedTrailer bits tail
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let m := 2 * l.1 + 2
  let n := 2 * l.1 + 4
  obtain ⟨value, hcf⟩ :=
    masterM_literal_workspace_markedPassed_decomposition w l tail
  refine ⟨value, ?_, ?_, ?_⟩
  · simpa [bits, trailer, cf, m, n, hcf, List.append_assoc] using
      runtimeFixedCleanupController_workspace retained tail bits value m n
  · exact runtimeFixedCleanupController_outer_final_halts
  · simpa [bits, trailer, cf, m, n, hcf, List.append_assoc] using
      runtimeFixedCleanupController_workspace_leftSafe retained tail bits value m n

#print axioms masterM_literal_fixedCleanup

/-- Scheduled nonterminal specialization of the fixed cleanup bridge.  In
addition to the physical run, this records that the compacted passed block is
exactly the canonical selected prefix for the next scheduled round. -/
theorem scheduled_masterM_literal_fixedCleanup
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (_htnext : t + 1 < (decodedLiterals x).length) :
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
    let m := 2 * l.1 + 2
    let n := 2 * l.1 + 4
    retained ++ flattenPairs (passedSourceBlock bits) =
      outputCap B out' ++
        selectedPrefix (B - (t + 1)) (schedule.take (t + 1)) ∧
    ∃ value,
      let workspace := runtimeWorkspaceFrontPairs value m n
      let clearClock := 2 * workspace.length + 6 + if value then 0 else 2
      let outerClock := runtimeFixedOuterControllerRoundsClock bits workspace.length
      let clock := (clearClock + 1) + outerClock
      let inputTape := retained ++ cf.tp
      let outputTape := retained ++ [false, false, false, false] ++
        flattenPairs (passedSourceBlock bits) ++
        flattenPairs (List.replicate workspace.length (false, false)) ++
        selectedTail rest
      run runtimeFixedCleanupControllerMachine clock
          ⟨runtimeFixedCleanupControllerMachine.start,
            retained.length, inputTape⟩ =
        ⟨RuntimeFixedCleanupControllerState.outer
            RuntimeFixedOuterControllerState.final,
          retained.length + 1, outputTape⟩ ∧
      runtimeFixedCleanupControllerMachine.halt
        (RuntimeFixedCleanupControllerState.outer
          RuntimeFixedOuterControllerState.final) = true ∧
      LeftSafeRun runtimeFixedCleanupControllerMachine
        ⟨runtimeFixedCleanupControllerMachine.start,
          retained.length, inputTape⟩ clock := by
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
  let m := 2 * l.1 + 2
  let n := 2 * l.1 + 4
  have hcanonical := scheduled_selectedPrefix_succ x w ht
  have hprefix : retained ++ flattenPairs (passedSourceBlock bits) =
      outputCap B out' ++
        selectedPrefix (B - (t + 1)) (schedule.take (t + 1)) := by
    simpa [retained, pre, B, schedule, preBlocks, bits, out',
      List.append_assoc] using congrArg (fun z => outputCap B out' ++ z)
        hcanonical.symm
  refine ⟨hprefix, ?_⟩
  simpa [bits, trailer, cf, l, m, n, retained, rest] using
    masterM_literal_fixedCleanup retained (selectedTail rest) w l

#print axioms scheduled_masterM_literal_fixedCleanup

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedCleanupScheduled
