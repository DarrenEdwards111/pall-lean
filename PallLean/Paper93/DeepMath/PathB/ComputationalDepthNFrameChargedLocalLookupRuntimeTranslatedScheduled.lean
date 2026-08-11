import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeTranslatedComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundTransition

/-!
# Scheduled specialization of translated marked repair

The generic translated controller is instantiated on the genuine completed
`masterM` workspace and the scheduled nonterminal archive.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTranslatedScheduled

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTranslatedComposition
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition

set_option maxHeartbeats 4000000 in
/-- On every scheduled nonterminal round, the genuine normalized cashout tape
runs through workspace translation, stale compaction, archive return, and
unary rebase.  The retained block after translation is definitionally the
canonical scheduled prefix for round `t+1`. -/
theorem scheduled_runtimeTranslatedMarkedUnary_run
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
    let d := (bits :: rest).length
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ selectedTail rest
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tclean := retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
      mcf.tp
    ∃ base unaryClock s,
      retained ++ flattenPairs (passedSourceBlock bits) =
        outputCap B out' ++
          selectedPrefix (B - (t + 1)) (schedule.take (t + 1)) ∧
      base.IsPrefix
        (retained ++ flattenPairs (passedSourceBlock bits) ++
          List.replicate (2 * (d + 2)) false) ∧
      run (runtimeTranslatedMarkedUnaryMachine bits d)
          (runtimeTranslatedMarkedPrefixClock bits d +
            runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d rest +
              1 + unaryClock)
          ⟨(runtimeTranslatedMarkedUnaryMachine bits d).start,
            retained.length, Tclean⟩ =
        ⟨s,
          (retained ++ flattenPairs (passedSourceBlock bits) ++
              List.replicate (2 * (d + 2)) false).length + 2 +
            (selectedTail rest).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      (runtimeTranslatedMarkedUnaryMachine bits d).halt s = true := by
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
  let d := (bits :: rest).length
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let old := mcf.tp.take (2 * bits.length + 4)
  let Tclean := retained ++ flattenPairs (runtimeMarkedStalePairs d) ++ mcf.tp
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hrestlen : rest.length = B - (t + 1) := by
    simp [rest, hslen]
  have hrestpos : 0 < rest.length := by omega
  obtain ⟨first, more, hrest⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hrestpos)
  have hbitslen : bits.length = 4 * l.1 + 8 := by
    simp [bits, literalLookupTape,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.encode,
      signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  obtain ⟨value, hworkspace⟩ :=
    masterM_literal_workspaceFrontPairs w l (selectedTail rest)
  let workspace := runtimeWorkspaceFrontPairs value (2 * l.1 + 2)
    (2 * l.1 + 4)
  have hold : old = flattenPairs workspace := by
    simpa [old, bits, trailer, mcf, workspace] using hworkspace
  have hworkspaceLen : workspace.length = bits.length + 2 := by
    simp [workspace, runtimeWorkspaceFrontPairs, hbitslen]
    omega
  have hlen : old.length = (flattenPairs (passedSourceBlock bits)).length := by
    rw [hold]
    simp [flattenPairs_length, hworkspaceLen, passedSourceBlock, dataPairs]
  have hmcfDrop : mcf.tp.drop bits.length = trailer := by
    simpa [bits, trailer, mcf] using masterM_literal_trailer w l trailer
  have hmcfTail : mcf.tp.drop (2 * bits.length + 4) = selectedTail rest := by
    rw [show 2 * bits.length + 4 = bits.length + (4 + bits.length) by omega,
      ← List.drop_drop, hmcfDrop]
    change List.drop (4 + bits.length)
      ([true, false, false, true] ++ List.replicate bits.length true ++
        selectedTail rest) = selectedTail rest
    rw [show 4 + bits.length =
      4 + (List.replicate bits.length true).length by simp,
      ← List.drop_drop]
    simp
  have hmcfSplit : mcf.tp = old ++ selectedTail rest := by
    rw [← List.take_append_drop (2 * bits.length + 4) mcf.tp,
      hmcfTail]
  have hfit : 2 * rest.length + 4 ≤
      (retained ++ flattenPairs (passedSourceBlock bits) ++
        List.replicate (2 * (d + 2)) false).length := by
    simp [d]
    omega
  have hrun := runtimeTranslatedMarkedUnary_run retained old bits first more d
    (by simpa using hlen) (by simpa [← hrest] using hfit)
  obtain ⟨base, unaryClock, s, hbase, hmachine, hhalt⟩ := hrun
  have hcanonical := scheduled_selectedPrefix_succ x w ht
  refine ⟨base, unaryClock, s, ?_, ?_, ?_, ?_⟩
  · simpa [retained, pre, B, schedule, preBlocks, bits, out',
      List.append_assoc] using congrArg (fun z => outputCap B out' ++ z)
        hcanonical.symm
  · exact hbase
  · have hmachine' := hmachine
    rw [← hrest] at hmachine'
    have hTclean : Tclean =
        retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
          old ++ selectedTail rest := by
      dsimp only [Tclean]
      rw [hmcfSplit]
      simp [List.append_assoc]
    change run (runtimeTranslatedMarkedUnaryMachine bits d)
        (runtimeTranslatedMarkedPrefixClock bits d +
          runtimeMarkedCompactArchiveClock (passedSourceBlock bits) d rest +
            1 + unaryClock)
        ⟨(runtimeTranslatedMarkedUnaryMachine bits d).start,
          retained.length, Tclean⟩ =
      ⟨s,
        (retained ++ flattenPairs (passedSourceBlock bits) ++
            List.replicate (2 * (d + 2)) false).length + 2 +
          (selectedTail rest).length,
        base ++ [false, true, false, true] ++
          sourceSelectorInput rest.length 0 rest⟩
    rw [hTclean]
    exact hmachine'
  · exact hhalt

#print axioms scheduled_runtimeTranslatedMarkedUnary_run

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTranslatedScheduled
