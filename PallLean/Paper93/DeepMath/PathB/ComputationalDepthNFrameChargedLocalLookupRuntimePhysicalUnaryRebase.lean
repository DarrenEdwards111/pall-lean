import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeUnaryRebaseWriter

/-!
# Physical fixed unary-rebase composition

This file joins the runtime-discovered archive seed endpoint to the fixed
archive-counted unary writer.  The only handoff is the ordinary
head-preserving transition of `headSeqMachine`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter

/-- One fixed controller from physical tape origin through archive discovery,
seed installation, archive-counted unary rebase, and restoration. -/
def outputWorkspaceArchiveReturnUnaryRebaseMachine : Machine :=
  headSeqMachine outputWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine

def outputWorkspaceArchiveReturnUnaryRebaseDone :
    outputWorkspaceArchiveReturnUnaryRebaseMachine.State := by
  unfold outputWorkspaceArchiveReturnUnaryRebaseMachine
  exact Sum.inr RuntimeUnaryRebaseState.done

set_option maxHeartbeats 1000000 in
theorem scheduledRuntimeRelativeOutput_physicalUnaryRebase
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
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    let seedClock := runtimeArchiveReturnSeedClock rest
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    ∃ base unaryClock,
      run outputWorkspaceArchiveReturnUnaryRebaseMachine
          ((prefixClock + 1 + seedClock) + 1 + unaryClock)
          (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp) =
        ⟨outputWorkspaceArchiveReturnUnaryRebaseDone,
          R + (selectedTail rest).length,
          base ++ [false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 +
    (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hseed := scheduledRuntimeRelativeOutput_physicalArchiveReturnSeed
    x w ht htnext
  obtain ⟨phys, a, b, hphys, hshape, hseedrun⟩ := hseed
  have hphys' : phys.length = R - 2 := by
    simpa [B, schedule, preBlocks, l, bits, rest, pre, R] using hphys
  have hrestlen : rest.length = B - (t + 1) := by
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    simp [rest, hslen]
  have hrestpos : 0 < rest.length := by
    rw [hrestlen]
    omega
  obtain ⟨first, more, hrest⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hrestpos)
  have hfit0 := scheduled_zeroCopyRebase_fits x w ht
  have hfit : 2 * rest.length + 2 ≤ phys.length := by
    have hs : 2 * rest.length + 2 ≤ pre.length + 2 * bits.length + 4 := by
      simpa [B, schedule, preBlocks, bits, rest, pre,
        zeroCopyRebasePrefix_length] using hfit0
    have hphysLower : pre.length + 2 * bits.length + 4 ≤ phys.length := by
      rw [hphys']
      omega
    exact le_trans hs hphysLower
  obtain ⟨base, unaryClock, hbase, hunary⟩ :=
    runtimeUnaryRebase_run_physical phys first more (by
      simpa [hrest] using hfit)
  have hR : phys.length + 2 = R := by
    have hRge : 2 ≤ R := by
      simp only [R]
      omega
    rw [hphys']
    exact Nat.sub_add_cancel hRge
  have hunary' : run runtimeUnaryRebaseMachine unaryClock
      ⟨RuntimeUnaryRebaseState.init1, R,
        phys ++ [false, true] ++ selectedTail rest⟩ =
      ⟨RuntimeUnaryRebaseState.done,
        R + (selectedTail rest).length,
        base ++ [false, true] ++ sourceSelectorInput rest.length 0 rest⟩ := by
    simpa [hrest, hR] using hunary
  have hjoin := headSeq_run outputWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine rcf.tp
    (phys ++ [false, true] ++ selectedTail rest)
    (base ++ [false, true] ++ sourceSelectorInput rest.length 0 rest)
    (prefixClock + 1 + seedClock) unaryClock R
    (R + (selectedTail rest).length)
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    RuntimeUnaryRebaseState.done
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R] using hseedrun)
    rfl hunary' rfl
  refine ⟨base, unaryClock, ?_⟩
  simpa [outputWorkspaceArchiveReturnUnaryRebaseMachine,
    outputWorkspaceArchiveReturnUnaryRebaseDone,
    B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
    lookupClock, M, routeClock, rcf, locateClock, tailClock,
    prefixClock, seedClock, R, hrestlen] using hjoin

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase.scheduledRuntimeRelativeOutput_physicalUnaryRebase
