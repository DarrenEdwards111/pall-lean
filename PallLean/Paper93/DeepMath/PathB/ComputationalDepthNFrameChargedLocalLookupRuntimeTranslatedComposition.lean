import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeWorkspaceTranslator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalLeftSafety

/-!
# Translate, compact, return, and unary-rebase composition

This module closes the control seam exposed by the semantic audit.  It first
overwrites the completed `masterM` workspace with the canonical passed-source
block, physically rewinds to the retained-prefix boundary, and then invokes
the already certified marked repair controller.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTranslatedComposition

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTranslator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

def runtimeTranslatedMarkedUnaryMachine (bits : List Bool) (d : Nat) : Machine :=
  let stale := flattenPairs (runtimeMarkedStalePairs d)
  let target := flattenPairs (passedSourceBlock bits)
  headSeqMachine (stageMachine stale.length target)
    (headSeqMachine
      (exactClockMachine runtimeCompactRewindMachine
        (stale.length + target.length))
      (runtimeMarkedCompactArchiveUnaryMachine (passedSourceBlock bits) d))

def runtimeTranslatedMarkedPrefixClock (bits : List Bool) (d : Nat) : Nat :=
  let stale := flattenPairs (runtimeMarkedStalePairs d)
  let target := flattenPairs (passedSourceBlock bits)
  (stale.length + target.length) + 1 +
    ((stale.length + target.length) + 1)

set_option maxHeartbeats 4000000 in
/-- The completed workspace is physically translated before the existing
marked compaction/archive/unary controller runs.  There are no state resets
or head teleports: both handoffs preserve the current head, and the explicit
rewind returns from the end of the translated block to `retained.length`. -/
theorem runtimeTranslatedMarkedUnary_run
    (retained old bits : List Bool) (first : List Bool)
    (more : List (List Bool)) (d : Nat)
    (hlen : old.length = (flattenPairs (passedSourceBlock bits)).length)
    (hfit : 2 * (first :: more).length + 4 ≤
      (retained ++ flattenPairs (passedSourceBlock bits) ++
        List.replicate (2 * (d + 2)) false).length) :
    ∃ base unaryClock s,
      base.IsPrefix
        (retained ++ flattenPairs (passedSourceBlock bits) ++
          List.replicate (2 * (d + 2)) false) ∧
      run (runtimeTranslatedMarkedUnaryMachine bits d)
          (runtimeTranslatedMarkedPrefixClock bits d +
            runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d
              (first :: more) + 1 + unaryClock)
          ⟨(runtimeTranslatedMarkedUnaryMachine bits d).start,
            retained.length,
            retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
              old ++ selectedTail (first :: more)⟩ =
        ⟨s,
          (retained ++ flattenPairs (passedSourceBlock bits) ++
              List.replicate (2 * (d + 2)) false).length + 2 +
            (selectedTail (first :: more)).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput (first :: more).length 0 (first :: more)⟩ ∧
      (runtimeTranslatedMarkedUnaryMachine bits d).halt s = true := by
  let stale := flattenPairs (runtimeMarkedStalePairs d)
  let target := flattenPairs (passedSourceBlock bits)
  let tail := selectedTail (first :: more)
  let T0 := retained ++ stale ++ old ++ tail
  let Ttranslated := retained ++ stale ++ target ++ tail
  let stageM := stageMachine stale.length target
  let rewindClock := stale.length + target.length
  let rewindM := exactClockMachine runtimeCompactRewindMachine rewindClock
  let repairM := runtimeMarkedCompactArchiveUnaryMachine
    (passedSourceBlock bits) d
  have hstage0 := stageMachine_run stale.length target (stale ++ old ++ tail)
  have hsafe := stageMachine_prefixSafe_any stale.length target
    (stale ++ old ++ tail) (stale.length + target.length)
  have hstageShift := run_shiftCfg stageM retained
    (init stageM (stale ++ old ++ tail)) (stale.length + target.length) (by
      simpa [stageM] using hsafe)
  have hstageBase : run stageM (stale.length + target.length)
      (init stageM (stale ++ old ++ tail)) =
    ⟨stageFinalState stale.length target,
      stale.length + target.length,
      stagedTape stale.length target target.length (stale ++ old ++ tail)⟩ := by
    simpa [stageM] using hstage0
  rw [hstageBase] at hstageShift
  have hreplace := stagedTape_replace_eq stale old target tail (by
    simpa [target] using hlen)
  rw [hreplace] at hstageShift
  have hstage : run stageM (stale.length + target.length)
      ⟨stageM.start, retained.length, T0⟩ =
    ⟨stageFinalState stale.length target,
      retained.length + stale.length + target.length, Ttranslated⟩ := by
    simpa [stageM, T0, Ttranslated, shiftCfg, init,
      Nat.add_assoc, List.append_assoc] using hstageShift
  have hrew0 := runtimeCompactRewind_run retained
    (stale ++ target ++ tail) rewindClock
  have hrew := exactClockMachine_run_of_run runtimeCompactRewindMachine
    rewindClock (retained.length + rewindClock) retained.length
    Ttranslated Ttranslated () (by intro; rfl) (by
      simpa [rewindClock, Ttranslated, List.append_assoc] using hrew0)
  obtain ⟨base, unaryClock, sr, hbase, hrepair, hrepairHalt⟩ :=
    runtimeMarkedCompactArchiveUnary_run retained (passedSourceBlock bits)
      first more d hfit
  let Tout := base ++ [false, true, false, true] ++
    sourceSelectorInput (first :: more).length 0 (first :: more)
  have hrepair' : run repairM
      (runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d
          (first :: more) + 1 + unaryClock)
      ⟨repairM.start, retained.length, Ttranslated⟩ =
    ⟨sr,
      (retained ++ flattenPairs (passedSourceBlock bits) ++
          List.replicate (2 * (d + 2)) false).length + 2 + tail.length,
      Tout⟩ := by
    simpa [repairM, Ttranslated, T0, stale, target, tail, Tout,
      List.append_assoc] using hrepair
  have hright := headSeq_run_at rewindM repairM
    Ttranslated Ttranslated Tout (retained.length + rewindClock)
    rewindClock
    (runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d
      (first :: more) + 1 + unaryClock)
    retained.length
    ((retained ++ flattenPairs (passedSourceBlock bits) ++
        List.replicate (2 * (d + 2)) false).length + 2 + tail.length)
    (⟨rewindClock, by omega⟩, ()) sr hrew
    (exactClockMachine_halt_at _ _ _) hrepair' hrepairHalt
  have hright' : run (headSeqMachine rewindM repairM)
      (rewindClock + 1 +
        (runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d
          (first :: more) + 1 + unaryClock))
      ⟨(headSeqMachine rewindM repairM).start,
        retained.length + stale.length + target.length, Ttranslated⟩ =
    ⟨Sum.inr sr,
      (retained ++ flattenPairs (passedSourceBlock bits) ++
          List.replicate (2 * (d + 2)) false).length + 2 + tail.length,
      Tout⟩ := by
    simpa [rewindClock, Nat.add_assoc] using hright
  have hall := headSeq_run_at stageM (headSeqMachine rewindM repairM)
    T0 Ttranslated Tout retained.length (stale.length + target.length)
    (rewindClock + 1 +
      (runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d
        (first :: more) + 1 + unaryClock))
    (retained.length + stale.length + target.length)
    ((retained ++ flattenPairs (passedSourceBlock bits) ++
        List.replicate (2 * (d + 2)) false).length + 2 + tail.length)
    (stageFinalState stale.length target) (Sum.inr sr) hstage
    (stageMachine_halt_final stale.length target) hright'
    (by simpa [headSeqMachine, repairM] using hrepairHalt)
  refine ⟨base, unaryClock, Sum.inr (Sum.inr sr), hbase, ?_, ?_⟩
  · simpa [runtimeTranslatedMarkedUnaryMachine,
      runtimeTranslatedMarkedPrefixClock, stageM, rewindM, repairM,
      rewindClock, stale, target, tail, T0, Tout, Nat.add_assoc] using hall
  · simpa [runtimeTranslatedMarkedUnaryMachine, headSeqMachine,
      rewindM, repairM] using hrepairHalt

/-- Composition rule for the translated controller's safety.  Translation
and the exact rewind are discharged internally; callers provide only the
already-certified repair-body safety and its terminal halt. -/
theorem runtimeTranslatedMarkedUnary_leftSafe_of_repair
    (retained old bits tail : List Bool) (d repairClock : Nat)
    (hlen : old.length = (flattenPairs (passedSourceBlock bits)).length)
    (hrepairSafe : LeftSafeRun
      (runtimeMarkedCompactArchiveUnaryMachine (passedSourceBlock bits) d)
      ⟨(runtimeMarkedCompactArchiveUnaryMachine
          (passedSourceBlock bits) d).start,
        retained.length,
        retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
          flattenPairs (passedSourceBlock bits) ++ tail⟩ repairClock)
    (hrepairHalt :
      (runtimeMarkedCompactArchiveUnaryMachine (passedSourceBlock bits) d).halt
        (run (runtimeMarkedCompactArchiveUnaryMachine
          (passedSourceBlock bits) d) repairClock
          ⟨(runtimeMarkedCompactArchiveUnaryMachine
              (passedSourceBlock bits) d).start,
            retained.length,
            retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
              flattenPairs (passedSourceBlock bits) ++ tail⟩).st = true) :
    LeftSafeRun (runtimeTranslatedMarkedUnaryMachine bits d)
      ⟨(runtimeTranslatedMarkedUnaryMachine bits d).start,
        retained.length,
        retained ++ flattenPairs (runtimeMarkedStalePairs d) ++ old ++ tail⟩
      (runtimeTranslatedMarkedPrefixClock bits d + repairClock) := by
  let stale := flattenPairs (runtimeMarkedStalePairs d)
  let target := flattenPairs (passedSourceBlock bits)
  let T0 := retained ++ stale ++ old ++ tail
  let Ttranslated := retained ++ stale ++ target ++ tail
  let stageM := stageMachine stale.length target
  let rewindClock := stale.length + target.length
  let rewindM := exactClockMachine runtimeCompactRewindMachine rewindClock
  let repairM := runtimeMarkedCompactArchiveUnaryMachine
    (passedSourceBlock bits) d
  have hstage0 := stageMachine_run stale.length target (stale ++ old ++ tail)
  have hp0 := stageMachine_prefixSafe_any stale.length target
    (stale ++ old ++ tail) (stale.length + target.length)
  have hl0 := stageMachine_leftSafe_any stale.length target
    (stale ++ old ++ tail) (stale.length + target.length)
  have hstageShift := run_shiftCfg stageM retained
    (init stageM (stale ++ old ++ tail)) (stale.length + target.length)
    (by simpa [stageM] using hp0)
  have hstageBase : run stageM (stale.length + target.length)
      (init stageM (stale ++ old ++ tail)) =
    ⟨stageFinalState stale.length target,
      stale.length + target.length,
      stagedTape stale.length target target.length (stale ++ old ++ tail)⟩ := by
    simpa [stageM] using hstage0
  rw [hstageBase] at hstageShift
  have hreplace := stagedTape_replace_eq stale old target tail (by
    simpa [target] using hlen)
  rw [hreplace] at hstageShift
  have hstage : run stageM (stale.length + target.length)
      ⟨stageM.start, retained.length, T0⟩ =
    ⟨stageFinalState stale.length target,
      retained.length + stale.length + target.length, Ttranslated⟩ := by
    simpa [stageM, T0, Ttranslated, shiftCfg, init,
      Nat.add_assoc, List.append_assoc] using hstageShift
  have hstageSafe : LeftSafeRun stageM
      ⟨stageM.start, retained.length, T0⟩
      (stale.length + target.length) := by
    simpa [stageM, T0, shiftCfg, init, List.append_assoc] using
      leftSafeRun_shiftCfg stageM retained
        (init stageM (stale ++ old ++ tail))
        (stale.length + target.length) (by simpa [stageM] using hp0)
        (by simpa [stageM] using hl0)
  have hrew0 := runtimeCompactRewind_run retained
    (stale ++ target ++ tail) rewindClock
  have hrew := exactClockMachine_run_of_run runtimeCompactRewindMachine
    rewindClock (retained.length + rewindClock) retained.length
    Ttranslated Ttranslated () (by intro; rfl) (by
      simpa [rewindClock, Ttranslated, List.append_assoc] using hrew0)
  have hrewSafe0 := runtimeCompactRewind_leftSafe retained
    (stale ++ target ++ tail) rewindClock
  have hrewSafe : LeftSafeRun rewindM
      ⟨rewindM.start, retained.length + rewindClock, Ttranslated⟩
      rewindClock := by
    simpa [rewindM, exactClockCfg] using
      exactClockMachine_leftSafe runtimeCompactRewindMachine rewindClock
        ⟨runtimeCompactRewindMachine.start,
          retained.length + rewindClock, Ttranslated⟩
        (by intro; rfl) (by
          simpa [Ttranslated, List.append_assoc] using hrewSafe0)
  have hinner := headSeq_leftSafe_at rewindM repairM
    Ttranslated Ttranslated (retained.length + rewindClock)
    rewindClock repairClock retained.length
    (⟨rewindClock, by omega⟩, ()) hrew
    (exactClockMachine_halt_at _ _ _) hrewSafe
    (by simpa [repairM, Ttranslated, stale, target,
      List.append_assoc] using hrepairSafe)
    (by simpa [repairM, Ttranslated, stale, target,
      List.append_assoc] using hrepairHalt)
  let repairCfg : Cfg repairM :=
    ⟨repairM.start, retained.length, Ttranslated⟩
  let repairFinal := run repairM repairClock repairCfg
  have hrepairHalt' : repairM.halt repairFinal.st = true := by
    simpa [repairM, repairFinal, repairCfg, Ttranslated, stale, target,
      List.append_assoc] using hrepairHalt
  have hinnerRun := headSeq_run_at rewindM repairM
    Ttranslated Ttranslated repairFinal.tp
    (retained.length + rewindClock) rewindClock repairClock
    retained.length repairFinal.hd
    (⟨rewindClock, by omega⟩, ()) repairFinal.st hrew
    (exactClockMachine_halt_at _ _ _)
    (by rfl) hrepairHalt'
  have hinnerHalt : (headSeqMachine rewindM repairM).halt
      (run (headSeqMachine rewindM repairM)
        (rewindClock + 1 + repairClock)
        ⟨(headSeqMachine rewindM repairM).start,
          retained.length + rewindClock, Ttranslated⟩).st = true := by
    rw [hinnerRun]
    simpa [headSeqMachine] using hrepairHalt'
  have houter := headSeq_leftSafe_at stageM
    (headSeqMachine rewindM repairM) T0 Ttranslated retained.length
    (stale.length + target.length) (rewindClock + 1 + repairClock)
    (retained.length + stale.length + target.length)
    (stageFinalState stale.length target) hstage
    (stageMachine_halt_final stale.length target) hstageSafe
    (by simpa [rewindClock, Nat.add_assoc] using hinner)
    (by simpa [rewindClock, Nat.add_assoc] using hinnerHalt)
  simpa [runtimeTranslatedMarkedUnaryMachine,
    runtimeTranslatedMarkedPrefixClock, stageM, rewindM, repairM,
    rewindClock, stale, target, T0, Nat.add_assoc] using houter

#print axioms runtimeTranslatedMarkedUnary_run
#print axioms runtimeTranslatedMarkedUnary_leftSafe_of_repair

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTranslatedComposition
